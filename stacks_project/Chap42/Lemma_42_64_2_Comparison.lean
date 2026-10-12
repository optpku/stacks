/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.ChowCohomology
public import stacks_project.Chap42.Lemma_42_54_5
public import stacks_project.Chap42.Lemma_42_64_1_IntersectionProduct

/-!
# Capping identity bivariant classes with the fundamental class

This file identifies `A^p(X)` with `CH_(r + 1 - p)(X)` for `X` smooth of relative
dimension `r` over a locally Dedekind base, by capping with `[X]_(r + 1)`, and
compares composition of bivariant classes with the self-intersection product.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open AlgebraicGeometry.Scheme.Modules hiding dual
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Dedekind

/-- Grading identity for composing a degree-`p` class with a degree-`-r` smooth
Gysin class. -/
theorem capFundamental_comp_degree (p : ℤ) (r : ℕ) :
    p + (-(r : ℤ)) = p - (r : ℤ) := sorry

/-- Grading identity relating the composite degree `1 - (p - r)` of capping with
`[S]₁` after composition with the structure morphism to the source degree
`r + 1 - p`. -/
theorem capFundamental_degree (r : ℕ) (p : ℤ) :
    1 - (p - (r : ℤ)) = (r : ℤ) + 1 - p := sorry

/-- The structure morphism of `Over.mk X.hom` as a map to the identity object
over `S`. -/
def structureToIdentity {S : Scheme.{u}} (X : Over S) :
    Over.mk X.hom ⟶ Over.mk (𝟙 S) :=
  Over.homMk (Over.mk X.hom).hom (Category.comp_id (Over.mk X.hom).hom)

/-- The underlying scheme morphism of `structureToIdentity X` is `X.hom`. -/
theorem structureToIdentity_left {S : Scheme.{u}} (X : Over S) :
    (structureToIdentity X).left = X.hom := sorry

/-- The identity object over `S` is locally of finite type over `S`. -/
instance instLocallyOfFiniteTypeOverMkId {S : Scheme.{u}} :
    LocallyOfFiniteType (Over.mk (𝟙 S)).hom := sorry

/-- `structureToIdentity X` is smooth whenever `X.hom` is smooth. -/
instance structureToIdentity_smooth {S : Scheme.{u}} (X : Over S)
    [Smooth X.hom] :
    Smooth (structureToIdentity X).left := sorry

/-- `structureToIdentity X` has the same relative dimension as `X.hom`. -/
instance structureToIdentity_relativeDimension {S : Scheme.{u}} (X : Over S)
    (r : ℕ) [RelativeDimension X.hom r] :
    RelativeDimension (structureToIdentity X).left r := sorry

/-- Cap of a degree-`p` identity bivariant class with the fundamental class
`[X]_(r + 1)`. -/
noncomputable def capFundamental
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (r : ℕ) (p : ℤ)
    (c : ChowCohomology.degree δ X.hom p) :
    RelativeChow δ X ((r : ℤ) + 1 - p) :=
  c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
    IsPullback.of_id_snd ((r : ℤ) + 1)
    (fundamentalClass_mk δ X.hom ((r : ℤ) + 1))

/-- Evaluation of `capFundamental` is the identity-square cap of `[X]_(r + 1)`. -/
theorem capFundamental_apply
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (r : ℕ) (p : ℤ)
    (c : ChowCohomology.degree δ X.hom p) :
    capFundamental δ X r p c =
      c.cap (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom)) (𝟙 (Over.mk X.hom))
        IsPullback.of_id_snd ((r : ℤ) + 1)
        (fundamentalClass_mk δ X.hom ((r : ℤ) + 1)) := sorry

/-- The zero identity class caps to the zero Chow class. -/
theorem capFundamental_zero
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (r : ℕ) (p : ℤ) :
    capFundamental δ X r p 0 = 0 := sorry

/-- Cap with `[X]_(r + 1)` preserves addition of identity bivariant classes. -/
theorem capFundamental_add
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (r : ℕ) (p : ℤ)
    (c d : ChowCohomology.degree δ X.hom p) :
    capFundamental δ X r p (c + d) =
      capFundamental δ X r p c + capFundamental δ X r p d := sorry

/-- Capping with `[X]_(r + 1)` as an additive map `A^p(X) →+ CH_(r + 1 - p)(X)`. -/
noncomputable def capFundamentalHom
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (r : ℕ) (p : ℤ) :
    ChowCohomology.degree δ X.hom p →+ RelativeChow δ X ((r : ℤ) + 1 - p) where
  toFun := capFundamental δ X r p
  map_zero' := capFundamental_zero δ X r p
  map_add' := capFundamental_add δ X r p

/-- The additive map `capFundamentalHom` is cap with `[X]_(r + 1)`. -/
theorem capFundamentalHom_apply
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (r : ℕ) (p : ℤ)
    (c : ChowCohomology.degree δ X.hom p) :
    capFundamentalHom δ X r p c = capFundamental δ X r p c := sorry

/-- Inverse of capping with `[X]_(r + 1)` on homogeneous identity classes. -/
noncomputable def capFundamentalInv
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [Smooth X.hom]
    (r : ℕ) [RelativeDimension X.hom r] (p : ℤ) :
    RelativeChow δ X ((r : ℤ) + 1 - p) → ChowCohomology.degree δ X.hom p :=
  Function.invFun (capFundamentalHom δ X r p)

/-- `capFundamentalInv` is the inverse function of `capFundamentalHom`. -/
theorem capFundamentalInv_apply
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [Smooth X.hom]
    (r : ℕ) [RelativeDimension X.hom r] (p : ℤ)
    (α : RelativeChow δ X ((r : ℤ) + 1 - p)) :
    capFundamentalInv δ X r p α =
      Function.invFun (capFundamentalHom δ X r p) α := sorry

/-- Capping with `[X]_(r + 1)` is inverted by `capFundamentalInv`. -/
theorem capFundamentalEquiv_left_inv
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X : Over S) [Smooth X.hom]
    (r : ℕ) [RelativeDimension X.hom r] (p : ℤ) :
    Function.LeftInverse (capFundamentalInv δ X r p)
      (capFundamentalHom δ X r p) := sorry

/-- `capFundamentalInv` is inverted by capping with `[X]_(r + 1)`. -/
theorem capFundamentalEquiv_right_inv
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X : Over S) [Smooth X.hom]
    (r : ℕ) [RelativeDimension X.hom r] (p : ℤ) :
    Function.RightInverse (capFundamentalInv δ X r p)
      (capFundamentalHom δ X r p) := sorry

/-- Additive identification `A^p(X) ≃+ CH_(r + 1 - p)(X)` by capping with
`[X]_(r + 1)`, for `X` smooth of relative dimension `r` over a locally Dedekind
base. -/
noncomputable def capFundamentalEquiv
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X : Over S) [Smooth X.hom]
    (r : ℕ) [RelativeDimension X.hom r] (p : ℤ) :
    ChowCohomology.degree δ X.hom p ≃+ RelativeChow δ X ((r : ℤ) + 1 - p) where
  toFun := capFundamentalHom δ X r p
  invFun := capFundamentalInv δ X r p
  left_inv := capFundamentalEquiv_left_inv δ h_delta X r p
  right_inv := capFundamentalEquiv_right_inv δ h_delta X r p
  map_add' := (capFundamentalHom δ X r p).map_add

/-- The forward map of `capFundamentalEquiv` is cap with `[X]_(r + 1)`. -/
theorem capFundamentalEquiv_apply
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X : Over S) [Smooth X.hom]
    (r : ℕ) [RelativeDimension X.hom r] (p : ℤ)
    (c : ChowCohomology.degree δ X.hom p) :
    capFundamentalEquiv δ h_delta X r p c = capFundamental δ X r p c := sorry

/-- The inverse of `capFundamentalEquiv` is `capFundamentalInv`. -/
theorem capFundamentalEquiv_symm_apply
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X : Over S) [Smooth X.hom]
    (r : ℕ) [RelativeDimension X.hom r] (p : ℤ)
    (α : RelativeChow δ X ((r : ℤ) + 1 - p)) :
    (capFundamentalEquiv δ h_delta X r p).symm α =
      capFundamentalInv δ X r p α := sorry

/-- `capFundamentalEquiv` is the composite of composition with the smooth Gysin
class of `X ⟶ S` and capping with `[S]₁`. -/
theorem capFundamentalEquiv_comp
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    (X : Over S) [Smooth X.hom]
    (r : ℕ) [RelativeDimension X.hom r] (p : ℤ)
    (c : ChowCohomology.degree δ X.hom p) :
    capFundamentalEquiv δ h_delta X r p c =
      castRelativeDegree δ (capFundamental_degree r p)
        ((Nonnegative.castGrading δ (capFundamental_comp_degree p r)
            (comp δ (𝟙 (Over.mk X.hom)) (structureToIdentity X) c
              (flatPullback δ (structureToIdentity X) r))).cap
          (𝟙 (Over.mk X.hom))
          (𝟙 (Over.mk X.hom) ≫ structureToIdentity X)
          (𝟙 (Over.mk (𝟙 S)))
          IsPullback.of_id_fst 1 (fundamentalClass_mk δ (𝟙 S) 1)) := sorry

end AlgebraicGeometry.BivariantClass.Dedekind

namespace AlgebraicGeometry.ChowGroup.Dedekind

/-- The comparison `X ×_X X ⟶ X` is the first projection of the identity
fiber product. -/
noncomputable abbrev intersectionProductSelfTo {S : Scheme.{u}} (X : Over S) :
    pullback (𝟙 X) (𝟙 X) ⟶ X :=
  pullback.fst (𝟙 X) (𝟙 X)

/-- `intersectionProductSelfTo` is the first projection of `X ×_X X`. -/
theorem intersectionProductSelfTo_eq {S : Scheme.{u}} (X : Over S) :
    intersectionProductSelfTo X = pullback.fst (𝟙 X) (𝟙 X) := sorry

/-- The first projection `X ×_X X ⟶ X` is proper. -/
instance intersectionProductSelfTo_isProper {S : Scheme.{u}} (X : Over S) :
    IsProper (intersectionProductSelfTo X).left := sorry

/-- The self-intersection product on total Chow homology of `X`, obtained by
specializing the product of Lemma 42.64.1 to `Y = Z = X` and pushing forward
along `X ×_X X ⟶ X`. -/
noncomputable def intersectionProductSelf
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X : Over S}
    [LocallyOfFiniteType X.hom] [Smooth X.hom]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (alpha beta : Total δ X) :
    Total δ X :=
  Total.map δ (intersectionProductSelfTo X)
    (intersectionProduct δ h_delta (𝟙 X) (𝟙 X) e D r alpha beta)

/-- `intersectionProductSelf` is the identity-fiber-product case of
`intersectionProduct`, pushed forward to `X`. -/
theorem intersectionProductSelf_def
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X : Over S}
    [LocallyOfFiniteType X.hom] [Smooth X.hom]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (alpha beta : Total δ X) :
    intersectionProductSelf δ h_delta e D r alpha beta =
      Total.map δ (intersectionProductSelfTo X)
        (intersectionProduct δ h_delta (𝟙 X) (𝟙 X) e D r alpha beta) := sorry

/-- Under `capFundamentalEquiv`, composition of homogeneous identity bivariant
classes becomes the self-intersection product on Chow homology. -/
theorem capFundamental_mul
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X : Over S}
    [Smooth X.hom]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (r : ℕ)
    [RelativeDimension X.hom r]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (p q : ℤ)
    (c : ChowCohomology.degree δ X.hom p)
    (c' : ChowCohomology.degree δ X.hom q) :
    intersectionProductSelf δ h_delta e D r
        (DirectSum.of (fun d : ℤ ↦ RelativeChow δ X d) ((r : ℤ) + 1 - p)
          (BivariantClass.Dedekind.capFundamentalEquiv δ h_delta X r p c))
        (DirectSum.of (fun d : ℤ ↦ RelativeChow δ X d) ((r : ℤ) + 1 - q)
          (BivariantClass.Dedekind.capFundamentalEquiv δ h_delta X r q c')) =
      DirectSum.of (fun d : ℤ ↦ RelativeChow δ X d) ((r : ℤ) + 1 - (p + q))
        (BivariantClass.Dedekind.capFundamentalEquiv δ h_delta X r (p + q)
          (ChowCohomology.mul δ X.hom c c')) := sorry

end AlgebraicGeometry.ChowGroup.Dedekind
