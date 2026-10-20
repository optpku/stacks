module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.CategoryTheory.Fibered.Groupoids.BaseProjection.Naturality
public import ReasLib.CategoryTheory.Fibered.Groupoids.Product
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.Postcompose
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Iso.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Coherence.Composition
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Functor

/-!
# Isom comparison along a morphism of algebraic stacks

For maps `x1, x2 : T ⟶ X`, the Isom object is the two-fibre product of the
diagonal of `T` against `T ×_X T ⟶ T ×_S T`. Postcomposition induces a
comparison between these Isom objects. Separation properties of the
postcomposing morphism control the properties of this comparison.
-/

@[expose] public section

-- Public constructions unfold through private componentwise isomorphism assemblies.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

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
      (baseProjection.naturality.{u + 1, u} x1).symm)
    (λ_ (baseProjection.{u + 1, u, u + 1} T.toGroupoids) ≪≫
      (baseProjection.naturality.{u + 1, u} x2).symm)

/-- The left vertex of `toSelfCospan x1 x2` is the identity of `T`. -/
theorem toSelfCospan_left {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (toSelfCospan x1 x2).left = 𝟙 T.toGroupoids :=
  rfl

/-- The right vertex of `toSelfCospan x1 x2` is the identity of `T`. -/
theorem toSelfCospan_right {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (toSelfCospan x1 x2).right = 𝟙 T.toGroupoids :=
  rfl

/-- The base vertex of `toSelfCospan x1 x2` is `baseProjection X`. -/
theorem toSelfCospan_base {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (toSelfCospan x1 x2).base = baseProjection.{u + 1, u, u + 1} X :=
  rfl

/-- The comparison `T ×_X T ⟶ T ×_S T` induced by the two maps `x1, x2`. -/
def toSelfProduct {S : Scheme.{u}} {X : GroupoidsOver S} {T : AlgebraicSpace S}
    (x1 x2 : T.toGroupoids ⟶ X) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} x1 x2 ⟶
      FiberedCategoryOver.Groupoids.prod T.toGroupoids T.toGroupoids :=
  TwoFibreProduct.map (toSelfCospan x1 x2)

/-- `toSelfProduct x1 x2` is the two-fibre-product map of `toSelfCospan x1 x2`. -/
theorem toSelfProduct_eq {S : Scheme.{u}} {X : GroupoidsOver S}
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    toSelfProduct x1 x2 = TwoFibreProduct.map (toSelfCospan x1 x2) :=
  rfl

/-- Left generating naturality for the identification of
`(TwoFibreProduct.postcomposeCospan x1 x2 f).comp (toSelfCospan (x1 ≫ f) (x2 ≫ f))` with
`toSelfCospan x1 x2`. -/
private theorem fibreProductCospan_comp_toSelfCospan_leftNaturality
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    ((λ_ (𝟙 T.toGroupoids)).hom ▷
        baseProjection.{u + 1, u, u + 1} T.toGroupoids) ≫
      (toSelfCospan x1 x2).leftIso.hom =
    ((TwoFibreProduct.postcomposeCospan.{u + 1, u, u + 1, u} x1 x2 f).comp
        (toSelfCospan (x1 ≫ f) (x2 ≫ f))).leftIso.hom ≫
      x1 ◁ (baseProjection.naturality.{u + 1, u} f).hom :=
  sorry

/-- Right generating naturality for the identification of
`(TwoFibreProduct.postcomposeCospan x1 x2 f).comp (toSelfCospan (x1 ≫ f) (x2 ≫ f))` with
`toSelfCospan x1 x2`. -/
private theorem fibreProductCospan_comp_toSelfCospan_rightNaturality
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    ((λ_ (𝟙 T.toGroupoids)).hom ▷
        baseProjection.{u + 1, u, u + 1} T.toGroupoids) ≫
      (toSelfCospan x1 x2).rightIso.hom =
    ((TwoFibreProduct.postcomposeCospan.{u + 1, u, u + 1, u} x1 x2 f).comp
        (toSelfCospan (x1 ≫ f) (x2 ≫ f))).rightIso.hom ≫
      x2 ◁ (baseProjection.naturality.{u + 1, u} f).hom :=
  sorry

/-- The composite cospan `(𝟙, 𝟙, f)` then `(𝟙, 𝟙, baseProjection Y)` is
isomorphic to `(𝟙, 𝟙, baseProjection X)`. -/
private def fibreProductCospan_comp_toSelfCospan_iso
    {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (TwoFibreProduct.postcomposeCospan.{u + 1, u, u + 1, u} x1 x2 f).comp (toSelfCospan (x1 ≫ f) (x2 ≫ f)) ≅
      toSelfCospan x1 x2 :=
  CospanTransform.Hom.isoMk (λ_ (𝟙 T.toGroupoids)) (λ_ (𝟙 T.toGroupoids))
    (baseProjection.naturality.{u + 1, u} f)
    (fibreProductCospan_comp_toSelfCospan_leftNaturality f x1 x2)
    (fibreProductCospan_comp_toSelfCospan_rightNaturality f x1 x2)

/-- The generating right comparison identifying
`TwoFibreProduct.mapPostcompose x1 x2 f ≫ toSelfProduct (x1 ≫ f) (x2 ≫ f)` with
`toSelfProduct x1 x2 ≫ 𝟙`. -/
private def isomCospan_rightIso {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} x1 x2 f ≫ toSelfProduct (x1 ≫ f) (x2 ≫ f) ≅
      toSelfProduct x1 x2 ≫ 𝟙 (FiberedCategoryOver.Groupoids.prod T.toGroupoids T.toGroupoids) :=
  (TwoFibreProduct.map.compIso (TwoFibreProduct.postcomposeCospan.{u + 1, u, u + 1, u} x1 x2 f)
      (toSelfCospan (x1 ≫ f) (x2 ≫ f))).symm ≪≫
    TwoFibreProduct.map.iso
      (fibreProductCospan_comp_toSelfCospan_iso f x1 x2) ≪≫
    (ρ_ (toSelfProduct x1 x2)).symm

/-- The cospan transformation with left identity on `T`, right
`TwoFibreProduct.mapPostcompose`, and identity on `T ×_S T`. -/
def isomCospan {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    CospanTransform (diagonal.{u + 1, u, u + 1} T.toGroupoids)
      (toSelfProduct x1 x2) (diagonal.{u + 1, u, u + 1} T.toGroupoids)
      (toSelfProduct (x1 ≫ f) (x2 ≫ f)) :=
  CospanTransform.mk (𝟙 T.toGroupoids) (TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} x1 x2 f)
    (𝟙 (FiberedCategoryOver.Groupoids.prod T.toGroupoids T.toGroupoids))
    (λ_ (diagonal.{u + 1, u, u + 1} T.toGroupoids) ≪≫
      (ρ_ (diagonal.{u + 1, u, u + 1} T.toGroupoids)).symm)
    (isomCospan_rightIso f x1 x2)

/-- The left vertex of `isomCospan f x1 x2` is the identity of `T`. -/
theorem isomCospan_left {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (isomCospan f x1 x2).left = 𝟙 T.toGroupoids :=
  rfl

/-- The right vertex of `isomCospan f x1 x2` is `TwoFibreProduct.mapPostcompose x1 x2 f`. -/
theorem isomCospan_right {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (isomCospan f x1 x2).right = TwoFibreProduct.mapPostcompose.{u + 1, u, u + 1, u} x1 x2 f :=
  rfl

/-- The base vertex of `isomCospan f x1 x2` is the identity of `T ×_S T`. -/
theorem isomCospan_base {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    (isomCospan f x1 x2).base = 𝟙 (FiberedCategoryOver.Groupoids.prod T.toGroupoids T.toGroupoids) :=
  rfl

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
  rfl

/-- The same-base Isom object of two morphisms to an algebraic stack is an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_isomApex {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {Z : AlgebraicSpace S}
    (x1 x2 : Z.toGroupoids ⟶ X) :
    IsRepresentableByAlgebraicSpace (AlgebraicStack.isomApex x1 x2) :=
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
  rfl

/-- If `f` is a separated morphism of algebraic stacks, then
`Isom_X(x1, x2) ⟶ Isom_Y(x1 ≫ f, x2 ≫ f)` is proper. -/
theorem isomComparison_proper {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Separated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S) (isomComparison f x1 x2) :=
  sorry

/-- If `f` is a quasi-separated morphism of algebraic stacks,
then `Isom_X(x1, x2) ⟶ Isom_Y(x1 ≫ f, x2 ≫ f)` is quasi-compact and
quasi-separated. -/
theorem isomComparison_quasiSeparated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
        (isomComparison f x1 x2) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (isomComparison f x1 x2) :=
  sorry

/-- The Isom comparison along a quasi-separated morphism is quasi-compact. -/
theorem isomComparison_quasiCompact {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
      (isomComparison f x1 x2) :=
  (isomComparison_quasiSeparated f x1 x2).1

/-- The Isom comparison along a quasi-separated morphism is quasi-separated. -/
theorem isomComparison_isQuasiSeparated {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiSeparated f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
      (isomComparison f x1 x2) :=
  (isomComparison_quasiSeparated f x1 x2).2

/-- If `f` is a quasi-DM morphism of algebraic stacks, then
`Isom_X(x1, x2) ⟶ Isom_Y(x1 ≫ f, x2 ≫ f)` is locally quasi-finite. -/
theorem isomComparison_locallyQuasiFinite {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiDM f] {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (isomComparison f x1 x2) :=
  sorry

/-- If `f` is a DM morphism of algebraic stacks, then
`Isom_X(x1, x2) ⟶ Isom_Y(x1 ≫ f, x2 ≫ f)` is unramified. -/
theorem isomComparison_unramified {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [DM f]
    {T : AlgebraicSpace S} (x1 x2 : T.toGroupoids ⟶ X) :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (isomComparison f x1 x2) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
