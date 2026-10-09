import Submission.PureXZ

namespace FLTCodec

def byteAt (input : ByteArray) (p : Nat) : Except String Nat :=
  if p < input.size then .ok input[p]!.toNat else .error "XZ input ended"

def littleEndian (input : ByteArray) (p count : Nat) : Except String Nat := do
  let mut n := 0
  for i in [:count] do n := n ||| ((← byteAt input (p + i)) <<< (8 * i))
  return n

def variableInteger (input : ByteArray) (start : Nat) : Except String (Nat × Nat) := do
  let mut n := 0
  let mut p := start
  for i in [:9] do
    let b ← byteAt input p
    p := p + 1
    n := n ||| ((b &&& 127) <<< (7 * i))
    if b < 128 then
      if i > 0 && b == 0 then throw "noncanonical XZ integer"
      return (n, p)
  throw "XZ integer too long"

def crc32Table : Array UInt32 := Id.run do
  let mut t := #[]
  for i in [:256] do
    let mut x := i.toUInt32
    for _ in [:8] do x := (x >>> 1) ^^^ (if x &&& 1 == 1 then 0xedb88320 else 0)
    t := t.push x
  return t

def crc64Table : Array UInt64 := Id.run do
  let mut t := #[]
  for i in [:256] do
    let mut x := i.toUInt64
    for _ in [:8] do x := (x >>> 1) ^^^ (if x &&& 1 == 1 then 0xc96c5795d7870f42 else 0)
    t := t.push x
  return t

def crc32 (input : ByteArray) (start stop : Nat) : UInt32 := Id.run do
  let mut crc : UInt32 := 0xffffffff
  let table := crc32Table
  for i in [start:stop] do
    crc := (crc >>> 8) ^^^ table[((crc.toNat ^^^ input[i]!.toNat) &&& 255)]!
  return crc ^^^ 0xffffffff

def crc64 (input : ByteArray) : UInt64 := Id.run do
  let mut crc : UInt64 := 0xffffffffffffffff
  let table := crc64Table
  for i in [:input.size] do
    crc := (crc >>> 8) ^^^ table[((crc.toNat ^^^ input[i]!.toNat) &&& 255)]!
  return crc ^^^ 0xffffffffffffffff

def requireZeroPadding (input : ByteArray) (start stop : Nat) : Except String Unit := do
  for i in [start:stop] do
    if (← byteAt input i) != 0 then throw "nonzero XZ padding"

def decodeXZ (input : ByteArray) : Except String ByteArray := do
  if input.size < 32 then throw "XZ stream too short"
  if input.extract 0 6 != ByteArray.mk #[253, 55, 122, 88, 90, 0] then throw "bad XZ magic"
  if (← byteAt input 6) != 0 then throw "unsupported XZ stream flags"
  let check ← byteAt input 7
  let checkSize := if check == 0 then 0 else if check == 1 then 4 else if check == 4 then 8 else 100
  if checkSize == 100 then throw "unsupported XZ check (only none/CRC32/CRC64)"
  if (← littleEndian input 8 4) != (crc32 input 6 8).toNat then throw "XZ header CRC mismatch"
  let mut p := 12
  let mut blocks : Array (Nat × Nat) := #[]
  let mut output := ByteArray.empty
  while (← byteAt input p) != 0 do
    let blockStart := p
    let headerSize := ((← byteAt input p) + 1) * 4
    let headerEnd := p + headerSize
    if headerEnd > input.size || headerSize < 8 then throw "invalid XZ block header size"
    if (← littleEndian input (headerEnd - 4) 4) != (crc32 input p (headerEnd - 4)).toNat then
      throw "XZ block header CRC mismatch"
    let flags ← byteAt input (p + 1)
    if flags &&& 63 != 0 then throw "only one LZMA2 filter is supported"
    p := p + 2
    let mut compressedSize? : Option Nat := none
    let mut uncompressedSize? : Option Nat := none
    if flags &&& 64 != 0 then
      let (n, q) ← variableInteger input p
      compressedSize? := some n
      p := q
    if flags &&& 128 != 0 then
      let (n, q) ← variableInteger input p
      uncompressedSize? := some n
      p := q
    let (filter, q) ← variableInteger input p
    let (propertySize, z) ← variableInteger input q
    if filter != 33 || propertySize != 1 then throw "XZ filter is not plain LZMA2"
    let property ← byteAt input z
    if property > 40 then throw "invalid LZMA2 dictionary property"
    let dictionary := if property == 40 then 0xffffffff else (2 + (property &&& 1)) <<< (property / 2 + 11)
    if z + 1 > headerEnd - 4 then throw "XZ filter exceeds header"
    requireZeroPadding input (z + 1) (headerEnd - 4)
    let (decoded, dataEnd) ← decodeLZMA2 input headerEnd dictionary
    let compressedSize := dataEnd - headerEnd
    if compressedSize?.isSome && compressedSize? != some compressedSize then throw "XZ compressed size mismatch"
    if uncompressedSize?.isSome && uncompressedSize? != some decoded.size then throw "XZ uncompressed size mismatch"
    let checkStart := dataEnd + ((4 - compressedSize % 4) % 4)
    requireZeroPadding input dataEnd checkStart
    let digest ← littleEndian input checkStart checkSize
    if check == 1 && digest != (crc32 decoded 0 decoded.size).toNat then throw "XZ block CRC32 mismatch"
    if check == 4 && digest != (crc64 decoded).toNat then throw "XZ block CRC64 mismatch"
    blocks := blocks.push (headerSize + compressedSize + checkSize, decoded.size)
    output := output ++ decoded
    p := checkStart + checkSize
    if p ≤ blockStart then throw "XZ block failed to advance"
  let indexStart := p
  let (count, q) ← variableInteger input (p + 1)
  if count != blocks.size then throw "XZ index block count mismatch"
  p := q
  for i in [:count] do
    let (unpadded, q) ← variableInteger input p
    let (uncompressed, z) ← variableInteger input q
    if (unpadded, uncompressed) != blocks[i]! then throw "XZ index block size mismatch"
    p := z
  let indexCRC := p + ((4 - (p - indexStart) % 4) % 4)
  requireZeroPadding input p indexCRC
  if (← littleEndian input indexCRC 4) != (crc32 input indexStart indexCRC).toNat then throw "XZ index CRC mismatch"
  let footer := indexCRC + 4
  if footer + 12 > input.size then throw "XZ footer missing"
  if (← littleEndian input footer 4) != (crc32 input (footer + 4) (footer + 10)).toNat then throw "XZ footer CRC mismatch"
  if (← littleEndian input (footer + 4) 4) != ((footer - indexStart) / 4 - 1) then throw "XZ footer backward size mismatch"
  if (← byteAt input (footer + 8)) != 0 || (← byteAt input (footer + 9)) != check then throw "XZ footer flags mismatch"
  if (← byteAt input (footer + 10)) != 89 || (← byteAt input (footer + 11)) != 90 then throw "XZ footer magic mismatch"
  requireZeroPadding input (footer + 12) input.size
  if (input.size - footer - 12) % 4 != 0 then throw "invalid XZ stream padding size"
  return output

end FLTCodec
