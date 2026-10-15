import Submission
namespace FixtureChallenge
theorem root (n : Nat) : n = n := Submission.fermat_last_theorem n
example (n : Nat) : n = n := by original_submission_refl
example (n : Nat) : n = n := by packed_refl
end FixtureChallenge
#print axioms FixtureChallenge.root
#print axioms Submission.fermat_last_theorem
