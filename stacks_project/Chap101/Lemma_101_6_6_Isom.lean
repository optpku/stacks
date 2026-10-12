/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Iso.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Coherence.Composition
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Functor
public import stacks_project.Chap101.Lemma_101_6_6_Comparison
public import stacks_project.Chap97.«97_12_5_1»

/-!
# Isom-space comparison along a morphism of algebraic stacks

For maps `x1, x2 : T ⟶ X`, the algebraic-space Isom object is the 2-fibre
product of `Δ_T` against `T ×_X T ⟶ T ×_S T`. A 1-morphism `f : X ⟶ Y`
induces `Isom_X(x1, x2) ⟶ Isom_Y(x1 ≫ f, x2 ≫ f)` as a base change of
`fibreProductComparison`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The 2-fibre product `T ×_S T` of an algebraic space with itself over the
identity fibration. -/
def selfFibreProduct {S : Scheme.{u}} (T : AlgebraicSpace S) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u}
    (baseProjection.{u + 1, u, u + 1} T.toGroupoids)
    (baseProjection.{u + 1, u, u + 1} T.toGroupoids)

/-- `selfFibreProduct T` is the 2-fibre product of the two base projections of
`T`. -/
theorem selfFibreProduct_eq {S : Scheme.{u}} (T : AlgebraicSpace S) :
    selfFibreProduct T =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (baseProjection.{u + 1, u, u + 1} T.toGroupoids)
        (baseProjection.{u + 1, u, u + 1} T.toGroupoids) :=
  sorry

/-- The cospan transformation `(x1, x2) ⟶ (baseProjection T, baseProjection T)`
with identity vertices on `T` and base `baseProjection X`. -/
def toSelfCospan {S : Scheme.{u}} {X : GroupoidsOver S} {T : AlgebraicSpace S}
    (x1 x2 : T.toGroupoids ⟶ X) :
    CospanTransform x1 x2
      (baseProjection.{u + 1, u, u + 1} T.toGroupoids)
      (baseProjection.{u + 1, u, u + 1} T.toGroupoids) :=
  CospanTransform.mk (𝟙 T.toGroupoids) (𝟙 T.toGroupoids)
    (baseProjection.{u + 1, u, u + 1} X)
    (λ_ (baseProjection.{u + 1, u, u + 1} T.toGroupoids) ≪≫
      eqToIso (comp_baseProjection x1).symm)
    (λ_ (baseProjection.{u + 1, u, u + 1} T.toGroupoids) ≪≫
      eqToIso (comp_baseProjection x2).symm)

/-- The left vertex of `toSelfCospan x1 x2` is the identity of `T`. -/
theorem toSelfCospan_left {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (toSelfCospan x1 x2).left = 𝟙 T.toGroupoids :=
  sorry

/-- The right vertex of `toSelfCospan x1 x2` is the identity of `T`. -/
theorem toSelfCospan_right {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (toSelfCospan x1 x2).right = 𝟙 T.toGroupoids :=
  sorry

/-- The base vertex of `toSelfCospan x1 x2` is `baseProjection X`. -/
theorem toSelfCospan_base {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (toSelfCospan x1 x2).base = baseProjection.{u + 1, u, u + 1} X :=
  sorry

/-- The comparison `T ×_X T ⟶ T ×_S T` induced by the two maps `x1, x2`. -/
def toSelfProduct {S : Scheme.{u}} {X : GroupoidsOver S} {T : AlgebraicSpace S}
    (x1 x2 : T.toGroupoids ⟶ X) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} x1 x2 ⟶ selfFibreProduct T :=
  TwoFibreProduct.map (toSelfCospan x1 x2)

/-- `toSelfProduct x1 x2` is the two-fibre-product map of `toSelfCospan x1 x2`. -/
theorem toSelfProduct_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    toSelfProduct x1 x2 = TwoFibreProduct.map (toSelfCospan x1 x2) :=
  sorry

/-- Left generating naturality for the identification of
`fibreProductCospan.comp (toSelfCospan (x1 ≫ f) (x2 ≫ f))` with
`toSelfCospan x1 x2`. -/
theorem fibreProductCospan_comp_toSelfCospan_leftNaturality
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    ((λ_ (𝟙 T.toGroupoids)).hom ▷
        baseProjection.{u + 1, u, u + 1} T.toGroupoids) ≫
      (toSelfCospan x1 x2).leftIso.hom =
    ((fibreProductCospan f x1 x2).comp
        (toSelfCospan (x1 ≫ f) (x2 ≫ f))).leftIso.hom ≫
      x1 ◁ (eqToIso (comp_baseProjection f)).hom :=
  sorry

/-- Right generating naturality for the identification of
`fibreProductCospan.comp (toSelfCospan (x1 ≫ f) (x2 ≫ f))` with
`toSelfCospan x1 x2`. -/
theorem fibreProductCospan_comp_toSelfCospan_rightNaturality
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    ((λ_ (𝟙 T.toGroupoids)).hom ▷
        baseProjection.{u + 1, u, u + 1} T.toGroupoids) ≫
      (toSelfCospan x1 x2).rightIso.hom =
    ((fibreProductCospan f x1 x2).comp
        (toSelfCospan (x1 ≫ f) (x2 ≫ f))).rightIso.hom ≫
      x2 ◁ (eqToIso (comp_baseProjection f)).hom :=
  sorry

/-- The composite cospan `(𝟙, 𝟙, f)` then `(𝟙, 𝟙, baseProjection Y)` is
isomorphic to `(𝟙, 𝟙, baseProjection X)`. -/
def fibreProductCospan_comp_toSelfCospan_iso
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (fibreProductCospan f x1 x2).comp (toSelfCospan (x1 ≫ f) (x2 ≫ f)) ≅
      toSelfCospan x1 x2 :=
  CospanTransform.Hom.isoMk (λ_ (𝟙 T.toGroupoids)) (λ_ (𝟙 T.toGroupoids))
    (eqToIso (comp_baseProjection f))
    (fibreProductCospan_comp_toSelfCospan_leftNaturality f x1 x2)
    (fibreProductCospan_comp_toSelfCospan_rightNaturality f x1 x2)

/-- The generating right comparison identifying
`fibreProductComparison ≫ toSelfProduct (x1 ≫ f) (x2 ≫ f)` with
`toSelfProduct x1 x2 ≫ 𝟙`. -/
def isomCospan_rightIso {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    fibreProductComparison f x1 x2 ≫ toSelfProduct (x1 ≫ f) (x2 ≫ f) ≅
      toSelfProduct x1 x2 ≫ 𝟙 (selfFibreProduct T) :=
  (TwoFibreProduct.map.compIso (fibreProductCospan f x1 x2)
      (toSelfCospan (x1 ≫ f) (x2 ≫ f))).symm ≪≫
    TwoFibreProduct.map.iso
      (fibreProductCospan_comp_toSelfCospan_iso f x1 x2) ≪≫
    (ρ_ (toSelfProduct x1 x2)).symm

/-- The cospan transformation with left identity on `T`, right
`fibreProductComparison`, and identity on `T ×_S T`. -/
def isomCospan {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    CospanTransform (diagonal.{u + 1, u, u + 1} T.toGroupoids)
      (toSelfProduct x1 x2) (diagonal.{u + 1, u, u + 1} T.toGroupoids)
      (toSelfProduct (x1 ≫ f) (x2 ≫ f)) :=
  CospanTransform.mk (𝟙 T.toGroupoids) (fibreProductComparison f x1 x2)
    (𝟙 (selfFibreProduct T))
    (λ_ (diagonal.{u + 1, u, u + 1} T.toGroupoids) ≪≫
      (ρ_ (diagonal.{u + 1, u, u + 1} T.toGroupoids)).symm)
    (isomCospan_rightIso f x1 x2)

/-- The left vertex of `isomCospan f x1 x2` is the identity of `T`. -/
theorem isomCospan_left {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (isomCospan f x1 x2).left = 𝟙 T.toGroupoids :=
  sorry

/-- The right vertex of `isomCospan f x1 x2` is `fibreProductComparison f x1 x2`. -/
theorem isomCospan_right {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (isomCospan f x1 x2).right = fibreProductComparison f x1 x2 :=
  sorry

/-- The base vertex of `isomCospan f x1 x2` is the identity of `T ×_S T`. -/
theorem isomCospan_base {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (isomCospan f x1 x2).base = 𝟙 (selfFibreProduct T) :=
  sorry

/-- The Isom object `Isom_X(x1, x2)` as the 2-fibre product of `Δ_T` against
`T ×_X T ⟶ T ×_S T`. -/
def isomApex {S : Scheme.{u}} {X : GroupoidsOver S} {T : AlgebraicSpace S}
    (x1 x2 : T.toGroupoids ⟶ X) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u}
    (diagonal.{u + 1, u, u + 1} T.toGroupoids) (toSelfProduct x1 x2)

/-- `isomApex x1 x2` is the 2-fibre product of `Δ_T` against `toSelfProduct x1 x2`. -/
theorem isomApex_spec {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    isomApex x1 x2 =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (diagonal.{u + 1, u, u + 1} T.toGroupoids) (toSelfProduct x1 x2) :=
  sorry

/-- The comparison `Isom_X(x1, x2) ⟶ Isom_Y(x1 ≫ f, x2 ≫ f)` induced by `f`. -/
def isomComparison {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    isomApex x1 x2 ⟶ isomApex (x1 ≫ f) (x2 ≫ f) :=
  TwoFibreProduct.map (isomCospan f x1 x2)

/-- `isomComparison f x1 x2` is the two-fibre-product map of `isomCospan f x1 x2`. -/
theorem isomComparison_eq {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    isomComparison f x1 x2 = TwoFibreProduct.map (isomCospan f x1 x2) :=
  sorry

/-- A scheme-slice test of `isomComparison f x1 x2` is a scheme-slice test of
the relative 2-diagonal of `f`. -/
theorem isomComparison_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {T : AlgebraicSpace S}
    (x1 x2 : T.toGroupoids ⟶ X) (P : MorphismProperty (AlgebraicSpace S))
    (hP : Groupoids.Hom.has P (Hom.diagonal.{u + 1, u, u + 1} f)) :
    Groupoids.Hom.has P (isomComparison f x1 x2) :=
  sorry


end AlgebraicGeometry.AlgebraicStack
