module

public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Computation

@[expose] public section

/-!
# Shift Computation for Functors Induced by Localizer Morphisms

The functor induced by a shift-compatible localizer morphism commutes with shifts.  This leaf
registers compatibility of its named comparison isomorphism with shifts for arbitrary localization
models and specializes mathlib's component formulas so callers need not supply an auxiliary
functor or comparison isomorphism.
-/

noncomputable section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w

namespace CategoryTheory.LocalizerMorphism

open Localization

variable {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Category.{v₃} D₁] [Category.{v₄} D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {M : Type w} [AddMonoid M]
  [HasShift C₁ M] [HasShift C₂ M] [HasShift D₁ M] [HasShift D₂ M]

namespace facIso

/-- for arbitrary compatible localization models, the canonical comparison of the
functor induced by a localizer morphism is compatible with shifts. -/
@[stacks 0GSL "shift compatibility of an induced localization comparison"]
instance homCommShift (Φ : LocalizerMorphism W₁ W₂)
    [Φ.functor.CommShift M]
    [W₁.IsCompatibleWithShift M] [W₂.IsCompatibleWithShift M]
    (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁] [L₁.CommShift M]
    (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂] [L₂.CommShift M] :
    NatTrans.CommShift (Φ.facIso L₁ L₂).hom M := sorry

end facIso

namespace localizedFunctor

/-- on an object coming from the source localization, the forward shift comparison
of the induced functor is computed from the localization comparisons and the original shift
comparison. -/
@[reassoc, stacks 0GSL "forward shift computation for an induced localization functor"]
theorem commShiftIso_hom_app (Φ : LocalizerMorphism W₁ W₂)
    [Φ.functor.CommShift M]
    [W₁.IsCompatibleWithShift M] [W₂.IsCompatibleWithShift M]
    (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁] [L₁.CommShift M]
    (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂] [L₂.CommShift M]
    (m : M) (X : C₁) :
    ((Φ.localizedFunctor L₁ L₂).commShiftIso m).hom.app (L₁.obj X) =
      (Φ.localizedFunctor L₁ L₂).map ((L₁.commShiftIso m).inv.app X) ≫
        (Φ.facIso L₁ L₂).inv.app (X⟦m⟧) ≫
          L₂.map ((Φ.functor.commShiftIso m).hom.app X) ≫
            (L₂.commShiftIso m).hom.app (Φ.functor.obj X) ≫
              ((Φ.facIso L₁ L₂).hom.app X)⟦m⟧' := sorry

/-- on an object coming from the source localization, the inverse shift comparison
of the induced functor is computed from the localization comparisons and the original inverse
shift comparison. -/
@[reassoc, stacks 0GSL "inverse shift computation for an induced localization functor"]
theorem commShiftIso_inv_app (Φ : LocalizerMorphism W₁ W₂)
    [Φ.functor.CommShift M]
    [W₁.IsCompatibleWithShift M] [W₂.IsCompatibleWithShift M]
    (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁] [L₁.CommShift M]
    (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂] [L₂.CommShift M]
    (m : M) (X : C₁) :
    ((Φ.localizedFunctor L₁ L₂).commShiftIso m).inv.app (L₁.obj X) =
      ((Φ.facIso L₁ L₂).inv.app X)⟦m⟧' ≫
        (L₂.commShiftIso m).inv.app (Φ.functor.obj X) ≫
          L₂.map ((Φ.functor.commShiftIso m).inv.app X) ≫
            (Φ.facIso L₁ L₂).hom.app (X⟦m⟧) ≫
              (Φ.localizedFunctor L₁ L₂).map ((L₁.commShiftIso m).hom.app X) := sorry

end localizedFunctor


end CategoryTheory.LocalizerMorphism
