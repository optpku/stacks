/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Functor.Left
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Model.Left
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Left-Derived Models as Functors of Pointwise Values

The objectwise comparison from an arbitrary left-derived model is assembled into a natural
isomorphism after precomposition with the localization functor.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- An arbitrary left-derived model, pulled back to the source, is naturally isomorphic to the
functor of pointwise left-derived values. -/
@[stacks 05SA "left-derived model natural isomorphism with pointwise values"]
noncomputable def LeftDerived.Value.modelNatIso
    (F : C ⥤ D) (S : MorphismProperty C) (LF : S.Localization ⥤ D)
    (α : S.Q ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α S]
    [F.HasPointwiseLeftDerivedFunctor S] :
    S.Q ⋙ LF ≅ LeftDerived.Value.functor F S :=
  NatIso.ofComponents (fun X ↦ LeftDerived.Value.modelIso F S LF α X)
    (fun f ↦ LeftDerived.Value.modelIso.hom_naturality F S LF α f)

namespace LeftDerived.Value.modelNatIso

/-- The forward component of the model natural isomorphism is the objectwise model comparison. -/
@[simp, stacks 05SA]
theorem hom_app
    (F : C ⥤ D) (S : MorphismProperty C) (LF : S.Localization ⥤ D)
    (α : S.Q ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α S]
    [F.HasPointwiseLeftDerivedFunctor S] (X : C) :
    (LeftDerived.Value.modelNatIso F S LF α).hom.app X =
      (LeftDerived.Value.modelIso F S LF α X).hom := sorry

/-- The inverse component of the model natural isomorphism is the inverse objectwise comparison. -/
@[simp, stacks 05SA]
theorem inv_app
    (F : C ⥤ D) (S : MorphismProperty C) (LF : S.Localization ⥤ D)
    (α : S.Q ⋙ LF ⟶ F) [LF.IsLeftDerivedFunctor α S]
    [F.HasPointwiseLeftDerivedFunctor S] (X : C) :
    (LeftDerived.Value.modelNatIso F S LF α).inv.app X =
      (LeftDerived.Value.modelIso F S LF α X).inv := sorry

end LeftDerived.Value.modelNatIso

end CategoryTheory.Functor
