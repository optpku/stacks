module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_20_1_Ring
public import stacks_project.Chap88.Definition_88_8_1_Derived

/-!
# Rig-étale algebras over a Noetherian pair

An object `B` of (88.2.0.2) is rig-étale over `(A, I)` when some power of `I`
acts by zero on the completed naive cotangent complex `NL_{B/A}^∧` in `D(B)`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Algebra.RigEtale

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Definition 88.8.1: Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
Let `B` be an object of (88.2.0.2). We say `B` is rig-étale over `(A, I)` if
there exists an integer `c ≥ 0` such that for all `a ∈ I ^ c` multiplication
by `a` on `NL_{B/A}^∧` is zero in `D(B)`. -/
@[stacks 0GAY]
theorem iff_exists_pow_smul_id (I : Ideal A) (B : Type u)
    [CommRing B] [Algebra A B] [TopologicallyFiniteType I B] :
    RigEtale I B ↔
      ∃ (c : ℕ) (ι : Type u) (_ : Fintype ι)
          (P : NaiveCotangent.Adic.Presentation A B I ι),
        ∀ a ∈ I ^ c,
          (algebraMap A B a) • 𝟙 (NaiveCotangent.Adic.naiveCotangentObject I P) = 0 :=
  sorry

end Algebra.RigEtale
