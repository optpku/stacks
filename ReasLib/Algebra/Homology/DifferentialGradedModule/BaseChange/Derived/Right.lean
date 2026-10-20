module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.BaseChange.Derived.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Right-Derived Base Change

This leaf owns the total right derived functor of ordinary ground-ring base change and its
canonical comparison with the left-derived model.
-/

@[expose] public section

noncomputable section

universe uR uS uA

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.BaseChange

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]

/-- Ordinary ground-ring base change admits a total right derived functor.  Property I
resolutions supply this for any functor defined on the DG homotopy category. -/
instance hasRightDerivedFunctor (A : CochainDGAlgebra.{uR, uA} R) :
    (sourceFunctor (S := S) A).HasRightDerivedFunctor
      (DifferentialGradedModule.quasiIso A) := sorry

/-- The canonical total right derived functor of ordinary ground-ring base change. -/
@[stacks 0BYZ "right-derived ground-ring base change for differential graded modules"]
noncomputable def rightDerivedFunctor (A : CochainDGAlgebra.{uR, uA} R) :
    CategoryTheory.Functor (DifferentialGradedModule.Derived.Category.{uR, max uA uS} A)
      (DifferentialGradedModule.Derived.Category.{uR, max uA uS} (algebra (S := S) A)) :=
  (sourceFunctor (S := S) A).totalRightDerived
    (DifferentialGradedModule.Derived.Q A) (DifferentialGradedModule.quasiIso A)

/-- The canonical unit from ordinary base change to its total right derived functor. -/
@[stacks 0BYZ "ordinary-to-right-derived base-change unit"]
noncomputable def rightDerivedUnit (A : CochainDGAlgebra.{uR, uA} R) :
    sourceFunctor (S := S) A ⟶
      DifferentialGradedModule.Derived.Q A ⋙ rightDerivedFunctor (S := S) A :=
  (sourceFunctor (S := S) A).totalRightDerivedUnit
    (DifferentialGradedModule.Derived.Q A) (DifferentialGradedModule.quasiIso A)

/-- The canonical ground-ring base-change model with its unit satisfies the universal property
of a total right derived functor. -/
instance rightDerivedFunctor_isRightDerived (A : CochainDGAlgebra.{uR, uA} R) :
    (rightDerivedFunctor (S := S) A).IsRightDerivedFunctor
      (rightDerivedUnit (S := S) A) (DifferentialGradedModule.quasiIso A) := sorry

/-- The canonical comparison from left-derived to right-derived ordinary base change.  It is
the unique descent of the composite of the left-derived counit and right-derived unit. -/
@[stacks 0BYZ "left-to-right derived base-change comparison"]
noncomputable def leftRightComparison (A : CochainDGAlgebra.{uR, uA} R) :
    derivedFunctor (S := S) A ⟶ rightDerivedFunctor (S := S) A :=
  (Localization.whiskeringLeftFunctor'
    (DifferentialGradedModule.Derived.Q A) (DifferentialGradedModule.quasiIso A)
    (DifferentialGradedModule.Derived.Category.{uR, max uA uS} (algebra (S := S) A))).preimage
      (derivedCounit (S := S) A ≫ rightDerivedUnit (S := S) A)

/-- Precomposing the left-to-right comparison with localization recovers the composite of the
canonical left-derived counit and right-derived unit. -/
theorem whiskerLeft_leftRightComparison (A : CochainDGAlgebra.{uR, uA} R) :
    Functor.whiskerLeft (DifferentialGradedModule.Derived.Q A)
        (leftRightComparison (S := S) A) =
      derivedCounit (S := S) A ≫ rightDerivedUnit (S := S) A := sorry

end DifferentialGradedModule.BaseChange
