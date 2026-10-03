import ChallengeDeps
import Lean.Elab.Tactic.Omega

/-!
Explicit four-coset model for the Promislow presentation.
The action and factor set are those of Gardam, arXiv:2102.11818v2, §3.1.
This submission dependency makes no claim of new mathematical content.
-/

namespace Submission.Promislow

inductive Coset where
  | one | a | b | ab
  deriving DecidableEq, Repr

open Coset

def addQ : Coset → Coset → Coset
  | one, r => r
  | a, one => a | a, a => one | a, b => ab | a, ab => b
  | b, one => b | b, a => ab | b, b => one | b, ab => a
  | ab, one => ab | ab, a => b | ab, b => a | ab, ab => one

structure Vec where
  x : ℤ
  y : ℤ
  z : ℤ
  deriving DecidableEq, Repr

@[ext] theorem Vec.ext (v w : Vec) (hx : v.x = w.x) (hy : v.y = w.y)
    (hz : v.z = w.z) : v = w := by
  cases v; cases w; cases hx; cases hy; cases hz; rfl

def zeroV : Vec := ⟨0, 0, 0⟩
def addV (v w : Vec) : Vec := ⟨v.x + w.x, v.y + w.y, v.z + w.z⟩
def negV (v : Vec) : Vec := ⟨-v.x, -v.y, -v.z⟩
def rho : Coset → Vec → Vec
  | one, v => v
  | a, v => ⟨v.x, -v.y, -v.z⟩
  | b, v => ⟨-v.x, v.y, -v.z⟩
  | ab, v => ⟨-v.x, -v.y, v.z⟩

def factor : Coset → Coset → Vec
  | one, _ => zeroV
  | _, one => zeroV
  | a, a => ⟨1, 0, 0⟩
  | a, b => zeroV
  | a, ab => ⟨1, 0, 0⟩
  | b, a => ⟨-1, 1, -1⟩
  | b, b => ⟨0, 1, 0⟩
  | b, ab => ⟨-1, 0, -1⟩
  | ab, a => ⟨0, -1, 1⟩
  | ab, b => ⟨0, -1, 0⟩
  | ab, ab => ⟨0, 0, 1⟩

theorem rho_add (q : Coset) (v w : Vec) :
    rho q (addV v w) = addV (rho q v) (rho q w) := by
  cases q <;> apply Vec.ext <;> simp [rho, addV] <;> omega

theorem rho_comp (q r : Coset) (v : Vec) :
    rho (addQ q r) v = rho q (rho r v) := by
  cases q <;> cases r <;> apply Vec.ext <;> simp [rho, addQ]

theorem factor_cocycle (q r s : Coset) :
    addV (factor q r) (factor (addQ q r) s) =
      addV (rho q (factor r s)) (factor q (addQ r s)) := by
  cases q <;> cases r <;> cases s <;> decide

structure E where
  v : Vec
  q : Coset
  deriving DecidableEq, Repr

@[ext] theorem E.ext (g h : E) (hv : g.v = h.v) (hq : g.q = h.q) : g = h := by
  cases g; cases h; cases hv; cases hq; rfl

def mulE (g h : E) : E :=
  ⟨addV (addV g.v (rho g.q h.v)) (factor g.q h.q), addQ g.q h.q⟩
def oneE : E := ⟨zeroV, one⟩
def invE (g : E) : E := ⟨negV (rho g.q (addV g.v (factor g.q g.q))), g.q⟩

instance : Group E where
  mul := mulE
  one := oneE
  inv := invE
  mul_assoc g h k := by
    change mulE (mulE g h) k = mulE g (mulE h k)
    rcases g with ⟨v, q⟩; rcases h with ⟨w, r⟩; rcases k with ⟨t, s⟩
    cases q <;> cases r <;> cases s <;> apply E.ext
    all_goals first
      | rfl
      | apply Vec.ext <;> (try simp only [mulE, addV, rho, factor, zeroV, addQ]) <;> omega
  one_mul g := by
    change mulE oneE g = g
    rcases g with ⟨v, q⟩; cases q <;> apply E.ext
    all_goals first | rfl | apply Vec.ext <;> simp [mulE, oneE, addV, rho, factor, zeroV, addQ]
  mul_one g := by
    change mulE g oneE = g
    rcases g with ⟨v, q⟩; cases q <;> apply E.ext
    all_goals first | rfl | apply Vec.ext <;> simp [mulE, oneE, addV, rho, factor, zeroV, addQ]
  inv_mul_cancel g := by
    change mulE (invE g) g = oneE
    rcases g with ⟨v, q⟩; cases q <;> apply E.ext
    all_goals first
      | rfl
      | apply Vec.ext <;> simp [mulE, invE, oneE, addV, negV, rho, factor, zeroV, addQ]

@[simp] theorem mul_def (g h : E) : g * h = mulE g h := rfl
@[simp] theorem one_def : (1 : E) = oneE := rfl
@[simp] theorem inv_def (g : E) : g⁻¹ = invE g := rfl

def ea : E := ⟨zeroV, a⟩
def eb : E := ⟨zeroV, b⟩

theorem relation_a : eb⁻¹ * ea ^ 2 * eb * ea ^ 2 = 1 := by
  decide

theorem relation_b : ea⁻¹ * eb ^ 2 * ea * eb ^ 2 = 1 := by
  decide

def generatorImage : UnitConjecture.generators → E
  | .a => ea
  | .b => eb

theorem relations_satisfied (w : FreeGroup UnitConjecture.generators)
    (hw : w ∈ UnitConjecture.relations) : FreeGroup.lift generatorImage w = 1 := by
  simp only [UnitConjecture.relations, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · simpa [map_mul, map_inv, map_pow, UnitConjecture.a, UnitConjecture.b,
      generatorImage] using relation_a
  · simpa [map_mul, map_inv, map_pow, UnitConjecture.a, UnitConjecture.b,
      generatorImage] using relation_b

/-- This homomorphism satisfies the presentation; injectivity is a separate obligation. -/
def encode : UnitConjecture.P →* E := PresentedGroup.toGroup relations_satisfied

def scaleV (n : ℕ) (v : Vec) : Vec := ⟨n * v.x, n * v.y, n * v.z⟩

theorem translation_pow (v : Vec) (n : ℕ) :
    (⟨v, one⟩ : E) ^ n = ⟨scaleV n v, one⟩ := by
  induction n with
  | zero =>
    apply E.ext
    · apply Vec.ext <;> simp [scaleV, oneE, zeroV]
    · rfl
  | succ n ih =>
    rw [pow_succ, ih]
    apply E.ext
    · apply Vec.ext <;>
        simp [mul_def, mulE, scaleV, addV, factor, rho, zeroV, Nat.cast_add, add_mul]
    · rfl

theorem translation_torsion (v : Vec) (n : ℕ) (hn : n ≠ 0)
    (h : (⟨v, one⟩ : E) ^ n = 1) : v = zeroV := by
  rw [translation_pow] at h
  have hv := congrArg E.v h
  have hnz : (n : ℤ) ≠ 0 := by simpa using hn
  apply Vec.ext
  · have hx := congrArg Vec.x hv
    exact (mul_eq_zero.mp hx).resolve_left hnz
  · have hy := congrArg Vec.y hv
    exact (mul_eq_zero.mp hy).resolve_left hnz
  · have hz := congrArg Vec.z hv
    exact (mul_eq_zero.mp hz).resolve_left hnz

theorem square_coset (g : E) : (g ^ 2).q = one := by
  rcases g with ⟨v, q⟩
  cases q <;> rfl

theorem square_eq_one (g : E) (h : g ^ 2 = 1) : g = 1 := by
  rcases g with ⟨v, q⟩
  cases q
  · have hv := congrArg E.v h
    apply E.ext
    · apply Vec.ext
      · have hx := congrArg Vec.x hv
        simp [pow_two, mul_def, one_def, mulE, oneE, addV, rho, factor, zeroV] at hx ⊢
        omega
      · have hy := congrArg Vec.y hv
        simp [pow_two, mul_def, one_def, mulE, oneE, addV, rho, factor, zeroV] at hy ⊢
        omega
      · have hz := congrArg Vec.z hv
        simp [pow_two, mul_def, one_def, mulE, oneE, addV, rho, factor, zeroV] at hz ⊢
        omega
    · rfl
  · have hx := congrArg (fun g : E => g.v.x) h
    simp [pow_two, mul_def, one_def, mulE, oneE, addV, rho, factor, zeroV] at hx
    omega
  · have hy := congrArg (fun g : E => g.v.y) h
    simp [pow_two, mul_def, one_def, mulE, oneE, addV, rho, factor, zeroV] at hy
    omega
  · have hz := congrArg (fun g : E => g.v.z) h
    simp [pow_two, mul_def, one_def, mulE, oneE, addV, rho, factor, zeroV] at hz
    omega

theorem torsion_free (g : E) (n : ℕ) (hn : n ≠ 0) (h : g ^ n = 1) : g = 1 := by
  have hs : (g ^ 2) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm 2 n, pow_mul, h, one_pow]
  have hc := square_coset g
  have he : g ^ 2 = ⟨(g ^ 2).v, one⟩ := E.ext _ _ rfl hc
  rw [he] at hs
  have hv := translation_torsion _ n hn hs
  apply square_eq_one g
  rw [he, hv]
  rfl

def scaleZ (i : ℤ) (v : Vec) : Vec := ⟨i * v.x, i * v.y, i * v.z⟩

theorem translation_zpow (v : Vec) (i : ℤ) :
    (⟨v, one⟩ : E) ^ i = ⟨scaleZ i v, one⟩ := by
  cases i with
  | ofNat n => simpa [scaleV, scaleZ] using translation_pow v n
  | negSucc n =>
    rw [zpow_negSucc, translation_pow]
    apply E.ext
    · apply Vec.ext <;>
        simp [inv_def, invE, negV, rho, addV, factor, zeroV, scaleV, scaleZ,
          Int.negSucc_eq, add_mul]
    · rfl

end Submission.Promislow
