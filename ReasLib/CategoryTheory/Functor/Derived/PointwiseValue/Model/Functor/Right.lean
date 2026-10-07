module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Functor.Right
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Model.Right
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Right-Derived Models as Functors of Pointwise Values

The objectwise comparison from an arbitrary right-derived model is assembled into a natural
isomorphism after precomposition with the localization functor.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- An arbitrary right-derived model, pulled back to the source, is naturally isomorphic to the
functor of pointwise right-derived values. -/
@[stacks 05SA "right-derived model natural isomorphism with pointwise values"]
noncomputable def RightDerived.Value.modelNatIso
    (F : C ⥤ D) (S : MorphismProperty C) (RF : S.Localization ⥤ D)
    (α : F ⟶ S.Q ⋙ RF) [RF.IsRightDerivedFunctor α S]
    [F.HasPointwiseRightDerivedFunctor S] :
    S.Q ⋙ RF ≅ RightDerived.Value.functor F S :=
  NatIso.ofComponents (fun X ↦ RightDerived.Value.modelIso F S RF α X)
    (fun f ↦ RightDerived.Value.modelIso.hom_naturality F S RF α f)

namespace RightDerived.Value.modelNatIso

/-- The forward component of the model natural isomorphism is the objectwise model comparison. -/
@[simp, stacks 05SA]
theorem hom_app
    (F : C ⥤ D) (S : MorphismProperty C) (RF : S.Localization ⥤ D)
    (α : F ⟶ S.Q ⋙ RF) [RF.IsRightDerivedFunctor α S]
    [F.HasPointwiseRightDerivedFunctor S] (X : C) :
    (RightDerived.Value.modelNatIso F S RF α).hom.app X =
      (RightDerived.Value.modelIso F S RF α X).hom := sorry

/-- The inverse component of the model natural isomorphism is the inverse objectwise comparison. -/
@[simp, stacks 05SA]
theorem inv_app
    (F : C ⥤ D) (S : MorphismProperty C) (RF : S.Localization ⥤ D)
    (α : F ⟶ S.Q ⋙ RF) [RF.IsRightDerivedFunctor α S]
    [F.HasPointwiseRightDerivedFunctor S] (X : C) :
    (RightDerived.Value.modelNatIso F S RF α).inv.app X =
      (RightDerived.Value.modelIso F S RF α X).inv := sorry

end RightDerived.Value.modelNatIso

end CategoryTheory.Functor
