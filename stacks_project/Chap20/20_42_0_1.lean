module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
import StacksCheckRecall

/-!
# Tensor/internal-Hom adjunction on derived module categories

@stack 08DI
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (ModuleDerived X)]
variable [BraidedCategory (ModuleDerived X)]
variable [MonoidalClosed (ModuleDerived X)]

/- The reusable owner is the source-order currying equivalence in every braided closed monoidal
category. -/
@[stacks 08DI "braided tensor/internal-Hom equivalence"]
#check @CategoryTheory.MonoidalClosed.braidedHomEquiv

/- Equation 20.42.0.1 (08DI), owner orientation. -/
@[stacks 08DI "derived tensor/internal-Hom Hom equivalence"]
#check
  (CategoryTheory.MonoidalClosed.braidedHomEquiv :
    ∀ K L M : ModuleDerived X,
      (K ⊗ L ⟶ M) ≃ (K ⟶ (ihom L).obj M))

/- Equation 20.42.0.1 (08DI), source orientation as printed in the Stacks Project. -/
@[stacks 08DI "source-order inverse equivalence"]
#check
  (fun (K L M : ModuleDerived X) ↦
    (CategoryTheory.MonoidalClosed.braidedHomEquiv K L M).symm)

/- The inverse evaluation formula is part of the same generic owner API and is available for
downstream rewriting without a ringed-space-specific wrapper. -/
@[stacks 08DI "inverse braided tensor/internal-Hom formula"]
#check @CategoryTheory.MonoidalClosed.braidedHomEquiv_symm_apply

end

end AlgebraicGeometry.RingedSpace
