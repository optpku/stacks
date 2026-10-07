module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Graded.FiniteProjective
public import ReasLib.CategoryTheory.Preadditive.CompactObject

/-!
# A compact object not represented by a finite graded-projective DG module
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DifferentialGradedModule.Derived

/-- Lemma 110.69.1: there exists a cochain DG algebra `(A, d)` and a compact
object `E` of `D(A, d)` that is not isomorphic in `D(A, d)` to the image of any
finite graded-projective DG `A`-module. -/
@[stacks 09R5]
theorem exists_compactObject_not_iso_finiteGradedProjective :
    ∃ (R : Type u) (_ : CommRing R) (A : CochainDGAlgebra.{u, v} R)
      (E : Category.{u, v} A),
      IsCompactObject E ∧
        ¬ ∃ (P : DifferentialGradedModule.{u, v} A),
            IsFiniteGradedProjective A P ∧
              Nonempty ((fromModules A).obj P ≅ E) :=
  sorry

/-- Compact objects of `D(A, d)` need not be represented by finite
graded-projective DG `A`-modules. -/
theorem not_forall_isCompactObject_iso_finiteGradedProjective :
    ¬ ∀ (R : Type u) [CommRing R] (A : CochainDGAlgebra.{u, v} R)
        (E : Category.{u, v} A),
      IsCompactObject E →
        ∃ (P : DifferentialGradedModule.{u, v} A),
          IsFiniteGradedProjective A P ∧
            Nonempty ((fromModules A).obj P ≅ E) :=
  sorry

end DifferentialGradedModule.Derived
