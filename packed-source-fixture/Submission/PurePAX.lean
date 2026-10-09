import Submission.PureXZContainer

namespace FLTCodec

structure ArchiveFile where
  path : String
  bytes : ByteArray
  deriving Inhabited

def utf8 (bytes : ByteArray) : Except String String :=
  match String.fromUTF8? bytes with
  | some text => .ok text
  | none => .error "archive field is not UTF-8"

def terminatedField (input : ByteArray) (start length : Nat) : Except String String := do
  let mut stop := start
  for i in [start:start + length] do
    if (← byteAt input i) != 0 && stop == i then stop := stop + 1
  utf8 (input.extract start stop)

def tarOctal (input : ByteArray) (start length : Nat) : Except String Nat := do
  let mut n := 0
  let mut ended := false
  for i in [start:start + length] do
    let b ← byteAt input i
    if b == 0 || b == 32 then ended := true
    else
      if ended || b < 48 || b > 55 then throw "invalid tar octal field"
      n := n * 8 + (b - 48)
  return n

def paxPath (bytes : ByteArray) : Except String (Option String) := do
  let mut p := 0
  let mut path? := none
  while p < bytes.size do
    let start := p
    let mut length := 0
    let mut digits := 0
    while (← byteAt bytes p) != 32 do
      let b ← byteAt bytes p
      if b < 48 || b > 57 then throw "invalid PAX record length"
      length := length * 10 + b - 48
      digits := digits + 1
      p := p + 1
    if digits == 0 || length ≤ p - start + 2 || start + length > bytes.size then
      throw "invalid PAX record boundary"
    if (← byteAt bytes (start + length - 1)) != 10 then throw "PAX record lacks newline"
    let text ← utf8 (bytes.extract (p + 1) (start + length - 1))
    if text.startsWith "path=" then path? := some (text.drop 5).toString
    p := start + length
  return path?

def decodePAX (input : ByteArray) : Except String (Array ArchiveFile) := do
  let mut p := 0
  let mut localPath? := none
  let mut globalPath? := none
  let mut files := #[]
  while p + 512 ≤ input.size do
    let header := input.extract p (p + 512)
    if header == ByteArray.mk (Array.replicate 512 0) then
      if p + 1024 > input.size then throw "tar missing second zero terminator"
      requireZeroPadding input p input.size
      return files
    let expected ← tarOctal input (p + 148) 8
    let mut checksum := 0
    for i in [:512] do
      checksum := checksum + (if i ≥ 148 && i < 156 then 32 else input[p + i]!.toNat)
    if checksum != expected then throw "tar header checksum mismatch"
    let size ← tarOctal input (p + 124) 12
    let fileStart := p + 512
    if fileStart + size > input.size then throw "tar file exceeds stream"
    let file := input.extract fileStart (fileStart + size)
    let kind ← byteAt input (p + 156)
    if kind == 120 || kind == 103 then
      let path? ← paxPath file
      if kind == 120 then localPath? := path?
      else if path?.isSome then globalPath? := path?
    else
      if kind != 0 && kind != 48 then throw "unsupported tar entry type"
      let name ← terminatedField input p 100
      let pathPrefix ← terminatedField input (p + 345) 155
      let headerPath := if pathPrefix.isEmpty then name else pathPrefix ++ "/" ++ name
      let path := localPath?.getD (globalPath?.getD headerPath)
      if path.isEmpty then throw "empty tar path"
      files := files.push { path, bytes := file }
      localPath? := none
    p := fileStart + ((size + 511) / 512) * 512
  throw "tar lacks zero terminator"

end FLTCodec
