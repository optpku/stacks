/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue

@[expose] public section

/-!
# Naturality at Identity Denominators

These are the direct rewrite forms of denominator-square naturality when both denominators are
identities.  They keep downstream computation arguments from rebuilding the same `CommSq` and
expose the right and left orientations symmetrically.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D) [S.ContainsIdentities]

/-- The identity-denominator legs of pointwise right-derived values are natural in the source
morphism. -/
@[stacks 05SA "identity-denominator right naturality"]
theorem Functor.RightDerived.Value.ι_id_naturality
    {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X]
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    CategoryTheory.Functor.RightDerived.Value.ι F S (𝟙 X) (S.id_mem X) ≫ CategoryTheory.Functor.RightDerived.Value.map F S f =
      F.map f ≫ CategoryTheory.Functor.RightDerived.Value.ι F S (𝟙 Y) (S.id_mem Y) := sorry

/-- The identity-denominator projections of pointwise left-derived values are natural in the
source morphism. -/
@[stacks 05SA "identity-denominator left naturality"]
theorem Functor.LeftDerived.Value.π_id_naturality
    {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X]
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    CategoryTheory.Functor.LeftDerived.Value.map F S f ≫
        CategoryTheory.Functor.LeftDerived.Value.π F S (𝟙 Y) (S.id_mem Y) =
      CategoryTheory.Functor.LeftDerived.Value.π F S (𝟙 X) (S.id_mem X) ≫ F.map f := sorry

/-- The right-derived leg relation for a square whose left edge is an identity.  This is the
identity-denominator specialization of `CategoryTheory.Functor.RightDerived.Value.map_comp_of_square`. -/
@[stacks 05SA "right identity-denominator square"]
theorem Functor.RightDerived.Value.ι_of_id_square
    {Y Y₁ Y₂ : D} (s : Y ⟶ Y₁) (s' : Y ⟶ Y₂) (hs : S s) (hs' : S s')
    (f' : Y₁ ⟶ Y₂) (sq : CommSq (𝟙 Y) s s' f')
    [F.HasPointwiseRightDerivedFunctorAt S Y] :
    CategoryTheory.Functor.RightDerived.Value.ι F S s hs =
      F.map f' ≫ CategoryTheory.Functor.RightDerived.Value.ι F S s' hs' := sorry

/-- The left-derived projection relation for a square whose right edge is an identity.  This is the
identity-denominator specialization of `CategoryTheory.Functor.LeftDerived.Value.map_comp_of_square`. -/
@[stacks 05SA "left identity-denominator square"]
theorem Functor.LeftDerived.Value.π_of_id_square
    {Y Y₁ Y₂ : D} (s : Y₁ ⟶ Y) (s' : Y₂ ⟶ Y) (hs : S s) (hs' : S s')
    (f' : Y₁ ⟶ Y₂) (sq : CommSq s f' (𝟙 Y) s')
    [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    CategoryTheory.Functor.LeftDerived.Value.π F S s' hs' =
      CategoryTheory.Functor.LeftDerived.Value.π F S s hs ≫ F.map f' := sorry


end CategoryTheory
