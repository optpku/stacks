/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.LimitPreserving
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MapsIntoAffineOpen
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative representability on locally Noetherian schemes

Representability of transformations between limit-preserving sheaves can be
detected after restriction to locally Noetherian schemes and on affine finite
type test objects mapping into an affine open of the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Over

universe u

namespace AlgebraicGeometry.StandardTopology

/-- A natural transformation on locally Noetherian schemes is representable on
all affine finite type test objects mapping into an affine open of the base
when each corresponding Yoneda pullback is represented in the same site. -/
def relativelyRepresentableOnAffineFiniteType {S : Scheme.{u}}
    {F G : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (a : F ⟶ G) : Prop :=
  ∀ (V : (locallyNoetherian S).FullSubcategory) [IsAffine V.obj.left]
    [LocallyOfFiniteType V.obj.hom],
    MapsIntoAffineOpen V.obj.hom →
      ∀ (ξ : uliftYoneda.{u + 1}.obj V ⟶ G),
        ∃ (W : (locallyNoetherian S).FullSubcategory) (p : W ⟶ V)
          (q : uliftYoneda.{u + 1}.obj W ⟶ F),
          IsPullback q (uliftYoneda.{u + 1}.map p) a ξ

/-- Representability on affine finite type test objects is equivalent to the
existence of represented pullback squares for every such object and every map
from its universe-lifted Yoneda presheaf to the target. -/
theorem relativelyRepresentableOnAffineFiniteType_iff {S : Scheme.{u}}
    {F G : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (a : F ⟶ G) :
    relativelyRepresentableOnAffineFiniteType a ↔
      ∀ (V : (locallyNoetherian S).FullSubcategory) [IsAffine V.obj.left]
        [LocallyOfFiniteType V.obj.hom],
        MapsIntoAffineOpen V.obj.hom →
          ∀ (ξ : uliftYoneda.{u + 1}.obj V ⟶ G),
            ∃ (W : (locallyNoetherian S).FullSubcategory) (p : W ⟶ V)
              (q : uliftYoneda.{u + 1}.obj W ⟶ F),
              IsPullback q (uliftYoneda.{u + 1}.map p) a ξ := Iff.rfl

/-- Over a locally Noetherian base, a transformation between limit-preserving
sheaves for a standard topology is representable if and only if its restriction
to locally Noetherian schemes is representable. -/
@[stacks 0GE5]
theorem relativelyRepresentable_restrict_iff (τ : StandardTopology)
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    {F' G' : (Over S)ᵒᵖ ⥤ Type (u + 1)}
    (hF' : isLimitPreservingSheaf τ S F') (hG' : isLimitPreservingSheaf τ S G')
    (a' : F' ⟶ G') :
    uliftYoneda.{u + 1}.relativelyRepresentable a' ↔
      uliftYoneda.{u + 1}.relativelyRepresentable ((restrictPresheaf S).map a') :=
  sorry

/-- Over a locally Noetherian base, the restriction of a transformation between
limit-preserving sheaves is representable if and only if it is representable on
affine finite type test objects mapping into an affine open of the base. -/
@[stacks 0GE5]
theorem relativelyRepresentable_restrict_iff_affineFiniteType
    (τ : StandardTopology) {S : Scheme.{u}} [IsLocallyNoetherian S]
    {F' G' : (Over S)ᵒᵖ ⥤ Type (u + 1)}
    (hF' : isLimitPreservingSheaf τ S F') (hG' : isLimitPreservingSheaf τ S G')
    (a' : F' ⟶ G') :
    uliftYoneda.{u + 1}.relativelyRepresentable ((restrictPresheaf S).map a') ↔
      relativelyRepresentableOnAffineFiniteType ((restrictPresheaf S).map a') :=
  sorry

end AlgebraicGeometry.StandardTopology
