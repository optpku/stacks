module

public import ReasLib.AlgebraicGeometry.BivariantClass.Additive
public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.ExteriorProduct
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set
open scoped Classical

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Dedekind

/-- The canonical morphism from a scheme over `S` to the identity object over `S`. -/
def baseMap {S : Scheme.{u}} (X : Over S) : X ⟶ Over.mk (𝟙 S) :=
  Over.homMk X.hom

/-- The underlying scheme morphism of `baseMap X` is the structure morphism of `X`. -/
theorem baseMap_left {S : Scheme.{u}} (X : Over S) :
    (baseMap X).left = X.hom := sorry

/-- The product projections over `S` form a pullback square against the structure maps
to the identity object over `S`. -/
theorem productIsPullback {S : Scheme.{u}} (X : Over S) {Y : Over S}
    (g : Y ⟶ Over.mk (𝟙 S)) :
    IsPullback ((Limits.prod.fst : X ⨯ Y ⟶ X).left)
      ((Limits.prod.snd : X ⨯ Y ⟶ Y).left) (baseMap X).left g.left := sorry

/-- The canonical pullback comparison with `X ⨯ Y` respects the structure maps to `S`. -/
theorem productIsoOfIsPullback_hom_base
    {S : Scheme.{u}} (X : Over S) {X' Y : Over S}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ Over.mk (𝟙 S))
    (square : IsPullback i.left f'.left (baseMap X).left g.left) :
    (square.isoIsPullback X.left Y.left (productIsPullback X g)).hom ≫
        (X ⨯ Y).hom = X'.hom := sorry

/-- The canonical isomorphism from a displayed cartesian representative over `S` to
the product representative. -/
noncomputable def productIsoOfIsPullback
    {S : Scheme.{u}} (X : Over S) {X' Y : Over S}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ Over.mk (𝟙 S))
    (square : IsPullback i.left f'.left (baseMap X).left g.left) :
    X' ≅ X ⨯ Y :=
  Over.isoMk (square.isoIsPullback X.left Y.left (productIsPullback X g))
    (productIsoOfIsPullback_hom_base X i f' g square)

/-- The product comparison followed by the first projection is the given map to `X`. -/
theorem productIsoOfIsPullback_hom_fst
    {S : Scheme.{u}} (X : Over S) {X' Y : Over S}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ Over.mk (𝟙 S))
    (square : IsPullback i.left f'.left (baseMap X).left g.left) :
    (productIsoOfIsPullback X i f' g square).hom ≫ Limits.prod.fst = i := sorry

/-- The product comparison followed by the second projection is the given map to `Y`. -/
theorem productIsoOfIsPullback_hom_snd
    {S : Scheme.{u}} (X : Over S) {X' Y : Over S}
    (i : X' ⟶ X) (f' : X' ⟶ Y) (g : Y ⟶ Over.mk (𝟙 S))
    (square : IsPullback i.left f'.left (baseMap X).left g.left) :
    (productIsoOfIsPullback X i f' g square).hom ≫ Limits.prod.snd = f' := sorry

/-- The grading identity for the Dedekind exterior product defining a degree-`p` cap. -/
theorem exteriorProductDegree (p n : ℤ) : (1 - p) + n - 1 = n - p := sorry

/-- The cap family determined by a Chow class over a locally Dedekind base: take the
Dedekind exterior product and transport from `X ⨯ Y'` to the displayed cartesian
representative. -/
noncomputable def ofChowCap
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (alpha : RelativeChow δ X (1 - p)) : CapFamily δ (baseMap X) p :=
  fun {X' Y'} _ _ i f' g _ square n ↦
    (ChowGroup.map δ (X ⨯ Y') X'
      (productIsoOfIsPullback X i f' g square).inv (n - p)).comp
      ((@ChowGroup.reindex (X ⨯ Y').left
          (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y').hom)
          ((X ⨯ Y').hom.relativeDimensionFunction δ) inferInstance _ _
          (exteriorProductDegree p n)).toAddMonoidHom.comp
        (ChowGroup.Dedekind.ExteriorProduct.pairing
          δ h_delta X Y' (1 - p) n alpha))

/-- Evaluation of the cap family attached to `alpha` is Dedekind exterior product
followed by degree transport and pushforward along the inverse product comparison. -/
theorem ofChowCap_apply
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (alpha : RelativeChow δ X (1 - p))
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk (𝟙 S))
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (baseMap X).left g.left)
    (n : ℤ) (beta : RelativeChow δ Y' n) :
    ofChowCap δ h_delta X p alpha i f' g square n beta =
      ChowGroup.map δ (X ⨯ Y') X'
        (productIsoOfIsPullback X i f' g square).inv (n - p)
        ((@ChowGroup.reindex (X ⨯ Y').left
            (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y').hom)
            ((X ⨯ Y').hom.relativeDimensionFunction δ) inferInstance _ _
            (exteriorProductDegree p n)).toAddMonoidHom
          (ChowGroup.Dedekind.ExteriorProduct.pairing
            δ h_delta X Y' (1 - p) n alpha beta)) := sorry

/-- Dedekind exterior-product cap families commute with proper pushforward. -/
theorem ofChowCap_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (alpha : RelativeChow δ X (1 - p)) :
    CompatibleWithProperPushforward δ (ofChowCap δ h_delta X p alpha) := sorry

/-- Dedekind exterior-product cap families commute with flat pullback. -/
theorem ofChowCap_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (alpha : RelativeChow δ X (1 - p)) :
    CompatibleWithFlatPullback δ (ofChowCap δ h_delta X p alpha) := sorry

/-- Dedekind exterior-product cap families commute with effective-Cartier Gysin pullback. -/
theorem ofChowCap_gysinCartier
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (alpha : RelativeChow δ X (1 - p)) :
    CompatibleWithCartierGysin δ (ofChowCap δ h_delta X p alpha) := sorry

/-- The bivariant class whose action is Dedekind exterior product with `alpha`. -/
noncomputable def ofChow
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (alpha : RelativeChow δ X (1 - p)) : BivariantClass δ (baseMap X) p where
  cap := ofChowCap δ h_delta X p alpha
  map_proper := ofChowCap_mapProper δ h_delta X p alpha
  pullback_flat := ofChowCap_pullbackFlat δ h_delta X p alpha
  gysin_cartier := ofChowCap_gysinCartier δ h_delta X p alpha

/-- The cap field of `ofChow` is its Dedekind exterior-product cap family. -/
theorem ofChow_cap
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (alpha : RelativeChow δ X (1 - p))
    {X' Y' : Over S} [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
    (i : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Over.mk (𝟙 S))
    [LocallyOfFiniteType g.left]
    (square : IsPullback i.left f'.left (baseMap X).left g.left)
    (n : ℤ) (beta : RelativeChow δ Y' n) :
    (ofChow δ h_delta X p alpha).cap i f' g square n beta =
      ofChowCap δ h_delta X p alpha i f' g square n beta := sorry

/-- The bivariant class associated to the zero Chow class is pointwise zero. -/
theorem ofChow_zero
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ) :
    ofChow δ h_delta X p 0 = pointwiseZero δ (baseMap X) p := sorry

/-- The Dedekind exterior-product bivariant-class construction preserves addition. -/
theorem ofChow_add
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (alpha beta : RelativeChow δ X (1 - p)) :
    ofChow δ h_delta X p (alpha + beta) =
      pointwiseAdd δ (baseMap X) p (ofChow δ h_delta X p alpha)
        (ofChow δ h_delta X p beta) := sorry

/-- Evaluation of a bivariant class on the degree-one fundamental class of `S`. -/
noncomputable def toChow
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (c : BivariantClass δ (baseMap X) p) : RelativeChow δ X (1 - p) :=
  c.cap (𝟙 X) (baseMap X) (𝟙 (Over.mk (𝟙 S)))
    IsPullback.of_id_fst 1
    (@chowClass (Over.mk (𝟙 S)).left
      (LocallyOfFiniteType.isLocallyNoetherian (Over.mk (𝟙 S)).hom)
      ((Over.mk (𝟙 S)).hom.relativeDimensionFunction δ) inferInstance 1
      (@CycleGroup.fundamental (Over.mk (𝟙 S)).left
        (LocallyOfFiniteType.isLocallyNoetherian (Over.mk (𝟙 S)).hom)
        ((Over.mk (𝟙 S)).hom.relativeDimensionFunction δ) 1))

/-- The value `toChow c` is the formal cap product `c ∩ [S]₁`. -/
theorem toChow_def
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (c : BivariantClass δ (baseMap X) p) :
    toChow δ h_delta X p c =
      c.cap (𝟙 X) (baseMap X) (𝟙 (Over.mk (𝟙 S)))
        IsPullback.of_id_fst 1
        (@chowClass (Over.mk (𝟙 S)).left
          (LocallyOfFiniteType.isLocallyNoetherian (Over.mk (𝟙 S)).hom)
          ((Over.mk (𝟙 S)).hom.relativeDimensionFunction δ) inferInstance 1
          (@CycleGroup.fundamental (Over.mk (𝟙 S)).left
            (LocallyOfFiniteType.isLocallyNoetherian (Over.mk (𝟙 S)).hom)
            ((Over.mk (𝟙 S)).hom.relativeDimensionFunction δ) 1)) := sorry

/-- Evaluation on `[S]₁` sends the explicit pointwise-zero bivariant class to zero. -/
theorem toChow_zero
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ) :
    toChow δ h_delta X p (pointwiseZero δ (baseMap X) p) = 0 := sorry

/-- Evaluation on `[S]₁` preserves explicit pointwise addition of bivariant classes. -/
theorem toChow_add
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (c d : BivariantClass δ (baseMap X) p) :
    toChow δ h_delta X p (pointwiseAdd δ (baseMap X) p c d) =
      toChow δ h_delta X p c + toChow δ h_delta X p d := sorry

/-- Evaluation on `[S]₁` recovers the Chow class used to define a Dedekind
exterior-product bivariant class. -/
theorem toChow_ofChow
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (h_dim : ∀ component : irreducibleComponents S,
      topologicalKrullDim component = 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (alpha : RelativeChow δ X (1 - p)) :
    toChow δ h_delta X p (ofChow δ h_delta X p alpha) = alpha := sorry

/-- A bivariant class over a locally Dedekind base is recovered from its value on
`[S]₁`. -/
theorem ofChow_toChow
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (h_dim : ∀ component : irreducibleComponents S,
      topologicalKrullDim component = 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (c : BivariantClass δ (baseMap X) p) :
    ofChow δ h_delta X p (toChow δ h_delta X p c) = c := sorry

/-- The canonical additive identification of degree-`p` bivariant classes over a
locally Dedekind base with degree-`1 - p` Chow classes. -/
noncomputable def chowEquiv
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (h_dim : ∀ component : irreducibleComponents S,
      topologicalKrullDim component = 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ) :
    BivariantClass δ (baseMap X) p ≃ RelativeChow δ X (1 - p) where
  toFun := toChow δ h_delta X p
  invFun := ofChow δ h_delta X p
  left_inv := ofChow_toChow δ h_delta h_dim X p
  right_inv := toChow_ofChow δ h_delta h_dim X p

/-- The forward map of `chowEquiv` is capping with `[S]₁`. -/
theorem chowEquiv_apply
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (h_dim : ∀ component : irreducibleComponents S,
      topologicalKrullDim component = 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (c : BivariantClass δ (baseMap X) p) :
    chowEquiv δ h_delta h_dim X p c = toChow δ h_delta X p c := sorry

/-- The inverse map of `chowEquiv` sends a Chow class to its Dedekind
exterior-product bivariant class. -/
theorem chowEquiv_symm_apply
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = if IsClosed ({s} : Set S) then 0 else 1)
    (h_dim : ∀ component : irreducibleComponents S,
      topologicalKrullDim component = 1)
    (X : Over S) [LocallyOfFiniteType X.hom] (p : ℤ)
    (alpha : RelativeChow δ X (1 - p)) :
    (chowEquiv δ h_delta h_dim X p).symm alpha = ofChow δ h_delta X p alpha := sorry

end AlgebraicGeometry.BivariantClass.Dedekind
