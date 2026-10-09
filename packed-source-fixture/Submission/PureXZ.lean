import Lean

/-! Executable pure Lean decoder prototype for the measured XZ/LZMA2 format.
No external codec, FFI, subprocess, network, or custom Lake entry is used.
The range/state layout follows the public XZ specification and LZMA model.
This is a runtime decoder, not a theorem asserting universal codec correctness.
-/
namespace FLTCodec

structure LZState where
  input : ByteArray := ByteArray.empty
  pos : Nat := 0
  range : UInt32 := 0xffffffff
  code : UInt32 := 0
  probs : Array Nat := #[]
  output : ByteArray := ByteArray.empty
  dictStart : Nat := 0
  dictSize : Nat := 268435456
  lc : Nat := 3
  lp : Nat := 0
  pb : Nat := 2
  state : Nat := 0
  r0 : Nat := 0
  r1 : Nat := 0
  r2 : Nat := 0
  r3 : Nat := 0
  deriving Inhabited

abbrev Decoder := StateT LZState (Except String)

def takeByte : Decoder Nat := do
  let s ← get
  if s.pos ≥ s.input.size then throw "compressed input ended"
  let b := s.input[s.pos]!.toNat
  modify fun s => { s with pos := s.pos + 1 }
  return b

def normalize : Decoder Unit := do
  if (← get).range < 0x1000000 then
    let b ← takeByte
    modify fun s => { s with range := s.range <<< 8, code := (s.code <<< 8) ||| b.toUInt32 }

def modelBit (i : Nat) : Decoder Nat := do
  normalize
  let s ← get
  if i ≥ s.probs.size then throw "probability index out of bounds"
  let p := s.probs[i]!
  let bound := (s.range >>> 11) * p.toUInt32
  if s.code < bound then
    set { s with range := bound, probs := s.probs.set! i (p + ((2048 - p) >>> 5)) }
    return 0
  else
    set { s with range := s.range - bound, code := s.code - bound, probs := s.probs.set! i (p - (p >>> 5)) }
    return 1

def tree (base bits : Nat) : Decoder Nat := do
  let mut symbol := 1
  for _ in [:bits] do
    let b ← modelBit (base + symbol)
    symbol := symbol * 2 + b
  return symbol - (1 <<< bits)

def reverseTree (base bits : Nat) : Decoder Nat := do
  let mut symbol := 1
  let mut value := 0
  for i in [:bits] do
    let b ← modelBit (base + symbol)
    symbol := symbol * 2 + b
    value := value ||| (b <<< i)
  return value

def directBits (bits : Nat) : Decoder Nat := do
  let mut value := 0
  for _ in [:bits] do
    normalize
    let s ← get
    let range := s.range >>> 1
    if s.code ≥ range then
      set { s with range, code := s.code - range }
      value := value * 2 + 1
    else
      set { s with range }
      value := value * 2
  return value

def matchLength (base ps : Nat) : Decoder Nat := do
  if (← modelBit base) == 0 then
    return (← tree (base + 2 + ps * 8) 3) + 2
  if (← modelBit (base + 1)) == 0 then
    return (← tree (base + 130 + ps * 8) 3) + 10
  return (← tree (base + 258) 8) + 18

def historyByte (distance : Nat) : Decoder UInt8 := do
  let s ← get
  if distance ≥ s.output.size - s.dictStart || distance ≥ s.dictSize then
    throw "invalid dictionary distance"
  return s.output[s.output.size - distance - 1]!

def appendByte (b : UInt8) : Decoder Unit :=
  modify fun s => { s with output := s.output.push b }

def copyMatch (distance length limit : Nat) : Decoder Unit := do
  if (← get).output.size + length > limit then throw "match exceeds chunk output size"
  for _ in [:length] do appendByte (← historyByte distance)

def literal : Decoder Unit := do
  let s ← get
  let position := s.output.size - s.dictStart
  let previous := if position == 0 then 0 else s.output[s.output.size - 1]!.toNat
  let context := ((position &&& ((1 <<< s.lp) - 1)) <<< s.lc) + (previous >>> (8 - s.lc))
  let base := 1846 + 768 * context
  let mut symbol := 1
  if s.state ≥ 7 then
    let mut matched := (← historyByte s.r0).toNat
    let mut matching := true
    for _ in [:8] do
      let mb := (matched >>> 7) &&& 1
      matched := (matched <<< 1) &&& 255
      let b ← modelBit (base + (if matching then (1 + mb) * 256 else 0) + symbol)
      symbol := symbol * 2 + b
      if mb != b then matching := false
  else
    symbol := (← tree base 8) + 256
  appendByte (symbol - 256).toUInt8
  modify fun s => { s with state := if s.state < 4 then 0 else if s.state < 10 then s.state - 3 else s.state - 6 }

def decodeSymbol (limit : Nat) : Decoder Unit := do
  let s ← get
  let ps := (s.output.size - s.dictStart) &&& ((1 <<< s.pb) - 1)
  if (← modelBit (s.state * 16 + ps)) == 0 then
    literal
    return
  if (← modelBit (192 + s.state)) == 0 then
    let length ← matchLength 818 ps
    let slot ← tree (432 + (min (length - 2) 3) * 64) 6
    let mut distance := slot
    if slot ≥ 4 then
      let bits := (slot >>> 1) - 1
      distance := (2 + (slot &&& 1)) <<< bits
      if slot < 14 then
        distance := distance + (← reverseTree (688 + distance - slot - 1) bits)
      else
        distance := distance + ((← directBits (bits - 4)) <<< 4) + (← reverseTree 802 4)
    if distance == 0xffffffff then throw "unexpected LZMA end marker in LZMA2"
    modify fun s => { s with r3 := s.r2, r2 := s.r1, r1 := s.r0, r0 := distance, state := if s.state < 7 then 7 else 10 }
    copyMatch distance length limit
  else
    if (← modelBit (204 + s.state)) == 0 then
      if (← modelBit (240 + s.state * 16 + ps)) == 0 then
        modify fun s => { s with state := if s.state < 7 then 9 else 11 }
        copyMatch s.r0 1 limit
        return
    else
      let mut distance := s.r1
      if (← modelBit (216 + s.state)) == 0 then
        modify fun s => { s with r1 := s.r0 }
      else
        if (← modelBit (228 + s.state)) == 0 then
          distance := s.r2
        else
          distance := s.r3
          modify fun s => { s with r3 := s.r2 }
        modify fun s => { s with r2 := s.r1, r1 := s.r0 }
      modify fun s => { s with r0 := distance }
    let length ← matchLength 1332 ps
    modify fun s => { s with state := if s.state < 7 then 8 else 11 }
    copyMatch (← get).r0 length limit

def resetModels : Decoder Unit := do
  modify fun s => { s with probs := Array.replicate (1846 + (768 <<< (s.lc + s.lp))) 1024, state := 0, r0 := 0, r1 := 0, r2 := 0, r3 := 0 }

def properties (p : Nat) : Decoder Unit := do
  if p ≥ 225 then throw "invalid LZMA properties"
  let lc := p % 9
  let lp := (p / 9) % 5
  let pb := p / 45
  if lc + lp > 4 then throw "LZMA2 lc+lp exceeds four"
  modify fun s => { s with lc, lp, pb }
  resetModels

def compressedChunk (compressed uncompressed : Nat) : Decoder Unit := do
  let start := (← get).pos
  if compressed < 5 || start + compressed > (← get).input.size then throw "invalid chunk size"
  if (← takeByte) != 0 then throw "invalid range coder initial byte"
  modify fun s => { s with range := 0xffffffff, code := 0 }
  for _ in [:4] do
    let b ← takeByte
    modify fun s => { s with code := (s.code <<< 8) ||| b.toUInt32 }
  let limit := (← get).output.size + uncompressed
  for _ in [:uncompressed] do
    if (← get).output.size < limit then decodeSymbol limit
    if (← get).pos > start + compressed then throw "range coder read beyond chunk"
  normalize
  let s ← get
  if s.output.size != limit || s.pos != start + compressed || s.code != 0 then
    throw s!"invalid chunk termination: output={s.output.size},limit={limit},pos={s.pos},end={start+compressed},code={s.code}"

partial def lzma2Loop (needDict needProps : Bool) : Decoder Unit := do
  let control ← takeByte
  if control == 0 then return
  let resetDict := control == 1 || control ≥ 224
  if needDict && !resetDict then throw "missing initial dictionary reset"
  if resetDict then modify fun s => { s with dictStart := s.output.size }
  if control < 128 then
    if control != 1 && control != 2 then throw "invalid uncompressed LZMA2 control"
    let hi ← takeByte
    let lo ← takeByte
    let length := hi * 256 + lo + 1
    for _ in [:length] do appendByte (← takeByte).toUInt8
    lzma2Loop false (needProps || resetDict)
  else
    let uh ← takeByte
    let ul ← takeByte
    let ch ← takeByte
    let cl ← takeByte
    let outputSize := (control &&& 31) * 65536 + uh * 256 + ul + 1
    let inputSize := ch * 256 + cl + 1
    if control ≥ 192 then properties (← takeByte)
    else
      if needProps || resetDict then throw "missing LZMA properties"
      if control ≥ 160 then resetModels
    compressedChunk inputSize outputSize
    lzma2Loop false false

def decodeLZMA2 (input : ByteArray) (position dictionary : Nat) : Except String (ByteArray × Nat) := do
  let (_, s) ← (lzma2Loop true true).run { input, pos := position, dictSize := dictionary }
  return (s.output, s.pos)

def base85Alphabet := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz!#$%&()*+-;<=>?@^_`{|}~"

def decodeBase85 (text : String) : Except String ByteArray := do
  let chars := text.toUTF8
  if chars.size % 5 != 0 then throw "base85 must be padded to five-byte chunks"
  let mut output := ByteArray.empty
  for i in [:chars.size / 5] do
    let mut n := 0
    for j in [:5] do
      let c := chars[i * 5 + j]!
      let mut value := 85
      for k in [:85] do
        if base85Alphabet.toUTF8[k]! == c then value := k
      if value == 85 then throw "invalid base85 character"
      n := n * 85 + value
    if n ≥ 4294967296 then throw "invalid base85 word"
    for j in [:4] do output := output.push ((n >>> ((3 - j) * 8)) &&& 255).toUInt8
  return output

end FLTCodec
