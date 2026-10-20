module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.FromModules
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Graded.FiniteProjective
public import ReasLib.CategoryTheory.Preadditive.CompactObject

/-!
# Compact Objects Not Represented by Finite Graded-Projective Modules
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DifferentialGradedModule.Derived

/-- Some compact objects in a derived category are not represented by finite graded-projective
differential graded modules. -/
theorem exists_compactObject_not_iso_finiteGradedProjective :
    ∃ (R : Type u) (_ : CommRing R) (A : CochainDGAlgebra.{u, v} R)
      (E : Category.{u, v} A),
      IsCompactObject E ∧
        ¬ ∃ (P : DifferentialGradedModule.{u, v} A),
            IsFiniteGradedProjective A P ∧
              Nonempty ((fromModules A).obj P ≅ E) :=
  sorry

end DifferentialGradedModule.Derived
