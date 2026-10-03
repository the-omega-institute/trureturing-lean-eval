import Submission.NormalForm
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-! Gardam's explicit inverse, checked over the four-coset group model. -/

namespace Submission.Promislow

noncomputable section

abbrev RE := MonoidAlgebra (ZMod 2) E

def basis (g : E) : RE := MonoidAlgebra.single g 1

def ex : E := ⟨⟨1, 0, 0⟩, .one⟩
def ey : E := ⟨⟨0, 1, 0⟩, .one⟩
def ez : E := ⟨⟨0, 0, 1⟩, .one⟩

def polyP : RE := (1 + basis ex) * (1 + basis ey) * (1 + basis ez⁻¹)
def polyQ : RE := basis ex⁻¹ * basis ey⁻¹ + basis ex + basis ey⁻¹ * basis ez + basis ez
def polyR : RE := 1 + basis ex + basis ey⁻¹ * basis ez + basis ex * basis ey * basis ez
def polyS : RE := 1 + (basis ex + basis ex⁻¹ + basis ey + basis ey⁻¹) * basis ez⁻¹

def unitE : RE := polyP + polyQ * basis ea + polyR * basis eb + polyS * basis (ea * eb)

def vOne : RE := basis ex⁻¹ * (basis ea⁻¹ * polyP * basis ea)
def vA : RE := (basis ex⁻¹ * polyQ) * basis ea
def vB : RE := (basis ey⁻¹ * polyR) * basis eb
def vAB : RE := (basis ez⁻¹ * (basis ea⁻¹ * polyS * basis ea)) * basis (ea * eb)
def uA : RE := polyQ * basis ea
def uB : RE := polyR * basis eb
def uAB : RE := polyS * basis (ea * eb)

def inverseE : RE := vOne + vA + vB + vAB

theorem left_coefficient_0 : vOne * polyP + vA * uA + vB * uB + vAB * uAB = 1 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.one_def, Finsupp.add_apply, Finsupp.single_apply,
    mul_def, inv_def, one_def, mulE, invE, oneE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide,
    show (17 : ZMod 2) = 1 from by decide]

theorem left_coefficient_1 : vOne * uA + vA * polyP + vB * uAB + vAB * uB = 0 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, mulE, invE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide,
    show (8 : ZMod 2) = 0 from by decide]

theorem left_coefficient_2 : vOne * uB + vA * uAB + vB * polyP + vAB * uA = 0 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, mulE, invE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (10 : ZMod 2) = 0 from by decide]

theorem left_coefficient_3 : vOne * uAB + vA * uB + vB * uA + vAB * polyP = 0 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, mulE, invE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide]

theorem inverseE_mul : inverseE * unitE = 1 := by
  calc
    inverseE * unitE = (vOne * polyP + vA * uA + vB * uB + vAB * uAB) + (vOne * uA + vA * polyP + vB * uAB + vAB * uB) + (vOne * uB + vA * uAB + vB * polyP + vAB * uA) + (vOne * uAB + vA * uB + vB * uA + vAB * polyP) := by
      simp only [inverseE, unitE, uA, uB, uAB, mul_add, add_mul]
      abel
    _ = 1 := by rw [left_coefficient_0, left_coefficient_1, left_coefficient_2, left_coefficient_3]; simp

theorem right_coefficient_0 : polyP * vOne + uA * vA + uB * vB + uAB * vAB = 1 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.one_def, Finsupp.add_apply, Finsupp.single_apply,
    mul_def, inv_def, one_def, mulE, invE, oneE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide,
    show (17 : ZMod 2) = 1 from by decide]

theorem right_coefficient_1 : polyP * vA + uA * vOne + uB * vAB + uAB * vB = 0 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, mulE, invE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (10 : ZMod 2) = 0 from by decide]

theorem right_coefficient_2 : polyP * vB + uA * vAB + uB * vOne + uAB * vA = 0 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, mulE, invE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide,
    show (8 : ZMod 2) = 0 from by decide]

theorem right_coefficient_3 : polyP * vAB + uA * vB + uB * vA + uAB * vOne = 0 := by
  classical
  simp only [vOne, vA, vB, vAB, uA, uB, uAB, polyP, polyQ, polyR, polyS, basis,
    mul_add, add_mul, mul_one, one_mul, MonoidAlgebra.single_mul_single]
  ext g
  simp only [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_single,
    MonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.single_apply,
    Finsupp.zero_apply, mul_def, inv_def, mulE, invE,
    ex, ey, ez, ea, eb, rho, factor, addQ, addV, negV, zeroV]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide,
    show (4 : ZMod 2) = 0 from by decide,
    show (6 : ZMod 2) = 0 from by decide]

theorem mul_inverseE : unitE * inverseE = 1 := by
  calc
    unitE * inverseE = (polyP * vOne + uA * vA + uB * vB + uAB * vAB) + (polyP * vA + uA * vOne + uB * vAB + uAB * vB) + (polyP * vB + uA * vAB + uB * vOne + uAB * vA) + (polyP * vAB + uA * vB + uB * vA + uAB * vOne) := by
      simp only [inverseE, unitE, uA, uB, uAB, mul_add, add_mul]
      abel
    _ = 1 := by rw [right_coefficient_0, right_coefficient_1, right_coefficient_2, right_coefficient_3]; simp

end
end Submission.Promislow
