/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.GroupoidTarget

/-!
# Representing 2-fibre products by morphisms of algebraic spaces

A 2-fibre product of categories fibred in groupoids over `(Sch/S)_fppf` may be
compared with a morphism of algebraic spaces representing the apex and the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A morphism `f' : F ⟶ G` of algebraic spaces over `S` represents the first
projection of the 2-fibre product of `g : Z ⟶ Y` with `f : X ⟶ Y` when `G`
represents `Z`, `F` represents the apex, and the induced 1-morphism of groupoid
fibrations is 2-isomorphic to `TwoFibreProduct.fst g f`. -/
def RepresentsTwoFibreProductOnSpace {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
    (F G : AlgebraicSpace S) (f' : F ⟶ G) : Prop :=
  ∃ (eZ : Z ≌ G.toGroupoids)
    (eApex : TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids),
    Nonempty
      (eApex.hom ≫ toGroupoids.map f' ≅
        TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f ≫ eZ.hom)

/-- Representing a 2-fibre product on spaces is equivalent to the existence of
representing equivalences whose projection triangle identifies `toGroupoids.map f'`
with `TwoFibreProduct.fst`. -/
theorem RepresentsTwoFibreProductOnSpace.iff {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {F G : AlgebraicSpace S} {f' : F ⟶ G} :
    RepresentsTwoFibreProductOnSpace f g F G f' ↔
      ∃ (eZ : Z ≌ G.toGroupoids)
        (eApex : TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids),
        Nonempty
          (eApex.hom ≫ toGroupoids.map f' ≅
            TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f ≫ eZ.hom) :=
  sorry

/-- The base of a 2-fibre product represented on spaces is equivalent to the
groupoid fibration of `G`. -/
theorem RepresentsTwoFibreProductOnSpace.exists_base {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {F G : AlgebraicSpace S} {f' : F ⟶ G}
    (h : RepresentsTwoFibreProductOnSpace f g F G f') :
    Nonempty (Z ≌ G.toGroupoids) :=
  sorry

/-- The apex of a 2-fibre product represented on spaces is equivalent to the
groupoid fibration of `F`. -/
theorem RepresentsTwoFibreProductOnSpace.exists_apex {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {F G : AlgebraicSpace S} {f' : F ⟶ G}
    (h : RepresentsTwoFibreProductOnSpace f g F G f') :
    Nonempty
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids) :=
  sorry

/-- The morphism of algebraic spaces recovers the first projection of the
2-fibre product up to the representing equivalences. -/
theorem RepresentsTwoFibreProductOnSpace.projection_triangle {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {F G : AlgebraicSpace S} {f' : F ⟶ G}
    (h : RepresentsTwoFibreProductOnSpace f g F G f') :
    ∃ (eZ : Z ≌ G.toGroupoids)
      (eApex : TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids),
      Nonempty
        (eApex.hom ≫ toGroupoids.map f' ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f ≫ eZ.hom) :=
  sorry

/-- Chosen representing equivalences and a 2-isomorphic projection triangle
yield a representation of the 2-fibre product on spaces. -/
theorem RepresentsTwoFibreProductOnSpace.of_equivalences {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {F G : AlgebraicSpace S} {f' : F ⟶ G}
    (eZ : Z ≌ G.toGroupoids)
    (eApex : TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids)
    (h : eApex.hom ≫ toGroupoids.map f' ≅
      TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f ≫ eZ.hom) :
    RepresentsTwoFibreProductOnSpace f g F G f' :=
  sorry

/-- The associated sheaves of isomorphism classes of the apex and of `Z` match
the functors of points of `F` and `G` after `uliftFunctor`, and
`BasedFunctor.fiberIsoClassMap` of `TwoFibreProduct.fst` corresponds to `f'`. -/
theorem RepresentsTwoFibreProductOnSpace.fiberIsoClass_ulift {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} {f : X ⟶ Y} {g : Z ⟶ Y}
    {F G : AlgebraicSpace S} {f' : F ⟶ G}
    (h : RepresentsTwoFibreProductOnSpace f g F G f') :
    ∃ (iZ : Functor.fiberIsoClassPresheaf Z.p ≅
        G.functorOfPoints ⋙ uliftFunctor.{u + 1, u})
      (iApex : Functor.fiberIsoClassPresheaf
          (p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f)) ≅
        F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}),
      BasedFunctor.fiberIsoClassMap
          (toBasedFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)) =
        iApex.hom ≫ Functor.whiskerRight f' uliftFunctor.{u + 1, u} ≫
          iZ.inv :=
  sorry

/-- A slice base change represented by an algebraic space over a scheme `U`
specializes the on-space comparison, with base representative `ofOver U`. -/
theorem RepresentsTwoFibreProductOnSpace.of_representsBaseChange
    {S : Scheme.{u}} {X Y : GroupoidsOver S} {f : X ⟶ Y} {U : Over S}
    {y : GroupoidsOver.slice U ⟶ Y} {Fy : AlgebraicSpace S}
    {fy : Fy ⟶ ofOver U} (h : RepresentsBaseChange f y Fy fy) :
    RepresentsTwoFibreProductOnSpace f y Fy (ofOver U) fy :=
  sorry

/-- Given algebraic-space representatives of the base and apex of a 2-fibre
product, its first projection corresponds to a morphism between those spaces.
The same morphism induces the canonical map on fiberwise isomorphism classes
under the lifted functors of points. -/
theorem RepresentsTwoFibreProductOnSpace.exists_morphism {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
    (F G : AlgebraicSpace S) (eZ : Z ≌ G.toGroupoids)
    (eApex : TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f ≌ F.toGroupoids) :
    ∃ f' : F ⟶ G,
      Nonempty
        (eApex.hom ≫ AlgebraicSpace.toGroupoids.map f' ≅
          TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f ≫ eZ.hom) ∧
      ∃ (iZ : Functor.fiberIsoClassPresheaf Z.p ≅
          G.functorOfPoints ⋙ uliftFunctor.{u + 1, u})
        (iApex : Functor.fiberIsoClassPresheaf
            (FiberedCategoryOver.Groupoids.p
              (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f)) ≅
          F.functorOfPoints ⋙ uliftFunctor.{u + 1, u}),
        BasedFunctor.fiberIsoClassMap
            (FiberedCategoryOver.Groupoids.toBasedFunctor
              (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f)) =
          iApex.hom ≫ Functor.whiskerRight f' uliftFunctor.{u + 1, u} ≫ iZ.inv :=
  sorry

end AlgebraicGeometry
