/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal.Comparison

/-!
# Explicit equivalence for the diagonal comparison

This module constructs the explicit inverse, unit, counit, and equivalence instance for the
canonical diagonal comparison of categorical pullbacks.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory.Limits

open Functor
open scoped CategoricalPullback

universe vA vB vC vD uA uB uC uD

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace CategoricalPullback

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace DiagonalComparison

namespace Implementation

/-- The outer pullback comparison identifies the left image
`F.obj X.fst.fst` with the chosen base object. -/
private def targetLeftIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    F.obj X.fst.fst ≅ X.snd :=
  (π₁ H H).mapIso X.iso

/-- The outer pullback comparison identifies the right image
`G.obj X.fst.snd` with the chosen base object. -/
private def targetRightIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    G.obj X.fst.snd ≅ X.snd :=
  (π₂ H H).mapIso X.iso

/-- Composing the two outer projection isomorphisms recovers the inner
comparison object of `A ×[C] B`. -/
private def recoveredIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    F.obj X.fst.fst ≅ G.obj X.fst.snd :=
  targetLeftIso F G H X ≪≫
    (targetRightIso F G H X).symm

/-- The recovered inner comparison is the composite of the two
projected outer isomorphisms. -/
@[simp] private theorem recoveredIso_hom
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : (toDiagonal F G H) ⊡ (Δₚ H)) :
    (recoveredIso F G H X).hom =
      (targetLeftIso F G H X).hom ≫
        (targetRightIso F G H X).inv := sorry
/- Proof strategy: unfold `recoveredIso`; the hom of a composite isomorphism is the composite
of the first hom with the second inverse. -/

/-- The left projection of a morphism in the outer pullback is exactly
the left naturality relation of the recovered base object. -/
private theorem targetLeftNaturality
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : (toDiagonal F G H) ⊡ (Δₚ H)}
    (f : X ⟶ Y) :
    F.map f.fst.fst ≫ (targetLeftIso F G H Y).hom =
      (targetLeftIso F G H X).hom ≫ f.snd := sorry
/- Proof strategy: unfold `targetLeftIso`, project the outer pullback compatibility equation
`f.w` to its first component with `CategoricalPullback.Hom.fst`, and simplify. -/

/-- The right projection of a morphism in the outer pullback is exactly
the right naturality relation of the recovered base object. -/
private theorem targetRightNaturality
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : (toDiagonal F G H) ⊡ (Δₚ H)}
    (f : X ⟶ Y) :
    G.map f.fst.snd ≫ (targetRightIso F G H Y).hom =
      (targetRightIso F G H X).hom ≫ f.snd := sorry
/- Proof strategy: unfold `targetRightIso`, project the outer pullback compatibility equation
`f.w` to its second component with `CategoricalPullback.Hom.snd`, and simplify. -/

/-- On comparison objects, the recovered inner isomorphism is the
original pullback isomorphism.

Proof strategy: expand the recovered composite, use the two comparison projection lemmas, and
cancel the identity and inverse factors. -/
@[simp] private theorem recoveredIso_comparison_hom
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    (recoveredIso F G H
        ((diagonalComparison F G H).obj X)).hom =
      X.iso.hom := sorry
/- Proof strategy: unfold `recoveredIso`, use `obj.iso.hom.fst` and `obj.iso.hom.snd`, then
normalize the identity and inverse factors. -/

/-- The recovered inner comparison is natural in morphisms of the outer
pullback.

Proof strategy: compose `targetLeftNaturality` with the inverse of
`targetRightNaturality` and reassociate. -/
private theorem recoveredIso_naturality
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : (toDiagonal F G H) ⊡ (Δₚ H)}
    (f : X ⟶ Y) :
    F.map f.fst.fst ≫ (recoveredIso F G H Y).hom =
      (recoveredIso F G H X).hom ≫ G.map f.fst.snd := sorry
/- Proof strategy: unfold `recoveredIso`, compose `targetLeftNaturality` with the inverse form of
`targetRightNaturality`, and reassociate. -/

-- Local declaration justification (source-local notation): this is the fixed codomain of
-- `diagonalComparison F G H` while this file builds its explicit inverse, unit, and counit.
-- Reusing the exact nested expression keeps those private data declarations definitionally on
-- the same target. The public comparison and equivalence signatures elaborate to that expression;
-- there is no independent target construction or consumer API for which a public alias would be
-- more than a wrapper.
local notation "Target(" F ", " G ", " H ")" =>
  (toDiagonal F G H) ⊡ (Δₚ H)

/-- The explicit object map of the inverse diagonal comparison. It keeps the two inner
projections and reconstructs their structural isomorphism from the two outer projections. -/
private def inverseObj
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : Target(F, G, H)) : F ⊡ G where
  fst := X.fst.fst
  snd := X.fst.snd
  iso := recoveredIso F G H X

/-- The explicit morphism map of the inverse diagonal comparison. -/
private def inverseMap
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : Target(F, G, H)} (f : X ⟶ Y) :
    inverseObj F G H X ⟶
      inverseObj F G H Y where
  fst := f.fst.fst
  snd := f.fst.snd
  w := recoveredIso_naturality F G H f

/-- `inverseMap` preserves identities.

Proof strategy: apply `CategoricalPullback.hom_ext`; both visible components are identities. -/
private theorem inverseMapId
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : Target(F, G, H)) :
    inverseMap F G H (𝟙 X) =
      𝟙 (inverseObj F G H X) := sorry
/- Proof strategy: apply `CategoricalPullback.hom_ext`; both visible components are identities. -/

/-- `inverseMap` preserves composition.

Proof strategy: pullback-morphism extensionality reduces the statement to componentwise
composition in `A` and `B`. -/
private theorem inverseMapComp
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y Z : Target(F, G, H)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    inverseMap F G H (f ≫ g) =
      inverseMap F G H f ≫
        inverseMap F G H g := sorry
/- Proof strategy: apply `CategoricalPullback.hom_ext`; both components reduce to composition in
`A` and `B`. -/

/-- The explicit inverse functor of the diagonal comparison:

It sends the explicit comparison target `Target(F, G, H)` back to the original pullback
`F ⊡ G`.

Unlike `Functor.inv`, its object and morphism data do not use `Classical.choice`. -/
private def inverse
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    Target(F, G, H) ⥤ F ⊡ G where
  obj := inverseObj F G H
  map := inverseMap F G H
  map_id := inverseMapId F G H
  map_comp := inverseMapComp F G H

/-- The two identity projection comparisons for the diagonal unit respect the pullback structural
isomorphism.

Proof strategy: unfold the recovered isomorphism on a comparison object and use
`recoveredIso_comparison_hom`; both projection transformations are
identities. -/
private theorem unitCoherence
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    whiskerRight
      (Iso.refl (𝟭 (F ⊡ G) ⋙ π₁ F G)).hom F ≫
          (associator _ _ _).hom ≫
          whiskerLeft
            (diagonalComparison F G H ⋙
              inverse F G H)
            (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
          (associator _ _ _).inv =
      (associator _ _ _).hom ≫
          whiskerLeft (𝟭 (F ⊡ G))
            (CatCommSq.iso (π₁ F G) (π₂ F G) F G).hom ≫
          (associator _ _ _).inv ≫
          whiskerRight
            (Iso.refl (𝟭 (F ⊡ G) ⋙ π₂ F G)).hom G := sorry
/- Proof strategy: unfold `diagonalComparison` and `inverse`; the two projection isomorphisms
are reflexive. Evaluate componentwise, use `recoveredIso_comparison_hom`, and normalize
associators and unitors. -/

/-- The explicit unit of the diagonal equivalence:

```
𝟭 (F ⊡ G) ≅ diagonalComparison F G H ⋙
  inverse F G H.
``` -/
private noncomputable def unitIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    𝟭 (F ⊡ G) ≅
      diagonalComparison F G H ⋙
        inverse F G H :=
  CategoricalPullback.mkNatIso
    (Iso.refl _)
    (Iso.refl _)
    (unitCoherence F G H)

/-- The named composite on which the explicit counit is defined. Keeping this functor opaque
prevents expensive unfolding of the two nested categorical pullbacks during elaboration. -/
private noncomputable def counitSourceFunctor
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    Target(F, G, H) ⥤ Target(F, G, H) :=
  inverse F G H ⋙
    diagonalComparison F G H

/-- Compatibility needed to compare the first outer components of the explicit counit.

Proof strategy: expand `recoveredIso`; the outer pullback relation gives
the equality after cancelling the right projection isomorphism. -/
private theorem counitFstComponentFac
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : Target(F, G, H)) :
    (F ⋙ H).map (𝟙 X.fst.fst) ≫ X.fst.iso.hom =
      ((counitSourceFunctor F G H).obj X).fst.iso.hom ≫
        (G ⋙ H).map (𝟙 X.fst.snd) := sorry
/- Proof strategy: unfold `recoveredIso` and `counitSourceFunctor`; use the outer pullback
relation and cancel the right projection isomorphism. -/

/-- The first-component isomorphism of the explicit counit. It is identity on the `A`- and
`B`-objects and compares only their structural pullback isomorphism. -/
private noncomputable def counitFstComponentIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : Target(F, G, H)) :
    ((counitSourceFunctor F G H).obj X).fst ≅ X.fst :=
  CategoricalPullback.mkIso (.refl _) (.refl _)
    (counitFstComponentFac F G H X)

/-- Compatibility of the two outer components of the explicit counit.

Proof strategy: project `X.iso` to its two components. The first component supplies
`targetLeftIso`; the second, together with the recovered inner isomorphism,
is exactly `counitFstComponentIso`. -/
private theorem counitComponentFac
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : Target(F, G, H)) :
    (toDiagonal F G H).map
          (counitFstComponentIso F G H X).hom ≫
        X.iso.hom =
      ((counitSourceFunctor F G H).obj X).iso.hom ≫
        (Δₚ H).map (targetLeftIso F G H X).hom := sorry
/- Proof strategy: project `X.iso` to both components; the first gives `targetLeftIso`, while the
second combines with `recoveredIso` to give `counitFstComponentIso`. -/

/-- The objectwise counit isomorphism of the explicit diagonal equivalence. -/
private noncomputable def counitComponentIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    (X : Target(F, G, H)) :
    (counitSourceFunctor F G H).obj X ≅ X :=
  CategoricalPullback.mkIso
    (counitFstComponentIso F G H X)
    (targetLeftIso F G H X)
    (counitComponentFac F G H X)

/-- Naturality of the explicit diagonal counit.

Proof strategy: apply nested `CategoricalPullback.hom_ext`; the inner components are identities,
and the outer component is `targetLeftNaturality`. -/
private theorem counitNaturality
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D)
    {X Y : Target(F, G, H)} (f : X ⟶ Y) :
    (counitSourceFunctor F G H).map f ≫
        (counitComponentIso F G H Y).hom =
      (counitComponentIso F G H X).hom ≫ f := sorry
/- Proof strategy: apply nested `CategoricalPullback.hom_ext`; the inner components are
identities and the outer component is `targetLeftNaturality`. -/

/-- The explicit counit of the diagonal equivalence:

```
inverse F G H ⋙
  diagonalComparison F G H ≅ 𝟭 (Target(F, G, H)).
``` -/
private noncomputable def counitIso
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    counitSourceFunctor F G H ≅
      𝟭 (Target(F, G, H)) :=
  NatIso.ofComponents (counitComponentIso F G H)
    (counitNaturality F G H)

/-- The triangle identity for the explicit diagonal unit and counit.

Proof strategy: evaluate at an inner pullback object and use `CategoricalPullback.hom_ext`; both
components reduce to identities. -/
private theorem triangle
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) (X : F ⊡ G) :
    (diagonalComparison F G H).map
          ((unitIso F G H).hom.app X) ≫
        (counitIso F G H).hom.app
          ((diagonalComparison F G H).obj X) =
      𝟙 ((diagonalComparison F G H).obj X) := sorry
/- Proof strategy: evaluate at `X` and apply nested `CategoricalPullback.hom_ext`; both visible
components reduce to identities. -/

end Implementation

/-- The explicit equivalence underlying the diagonal comparison:

```
F ⊡ G ≌ (toDiagonal F G H) ⊡ (Δₚ H).
```

All non-Prop object and morphism data are explicit; `sorryAx` is confined to functoriality,
naturality, compatibility, and triangle proof fields. -/
noncomputable def equivalence
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    F ⊡ G ≌ (toDiagonal F G H) ⊡ (Δₚ H) :=
  Equivalence.mk'
    (diagonalComparison F G H)
    (Implementation.inverse F G H)
    (Implementation.unitIso F G H)
    (Implementation.counitIso F G H)
    (Implementation.triangle F G H)

/-- The forward functor of the explicit diagonal equivalence is the canonical diagonal
comparison. -/
@[simp]
theorem equivalence.functor
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (equivalence F G H).functor =
      diagonalComparison F G H := sorry

/-- The inverse equivalence functor forgets to the nested left projection on its first leg. -/
noncomputable def inverseFstIso (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (equivalence F G H).inverse ⋙ π₁ F G ≅
      π₁ (toDiagonal F G H) (Δₚ H) ⋙ π₁ (F ⋙ H) (G ⋙ H) :=
  Iso.refl _

/-- The inverse equivalence functor forgets to the nested right projection on its second leg. -/
noncomputable def inverseSndIso (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (equivalence F G H).inverse ⋙ π₂ F G ≅
      π₁ (toDiagonal F G H) (Δₚ H) ⋙ π₂ (F ⋙ H) (G ⋙ H) :=
  Iso.refl _

/-- The canonical diagonal comparison is an equivalence.

Proof strategy: use the forward functor of `DiagonalComparison.equivalence`. -/
instance isEquivalence
    (F : A ⥤ C) (G : B ⥤ C) (H : C ⥤ D) :
    (diagonalComparison F G H).IsEquivalence := sorry
/- Proof strategy: transfer the canonical instance on the forward functor of
`DiagonalComparison.equivalence F G H`, which is definitionally `diagonalComparison F G H`. -/

end DiagonalComparison

end CategoricalPullback

end CategoryTheory.Limits
