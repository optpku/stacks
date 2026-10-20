module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import ReasLib.AlgebraicGeometry.BivariantClass.Restriction
public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.ExteriorProduct
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.BivariantClass.RegularImmersion
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.Commutation
public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.ExteriorProduct.Cap

/-!
# Intersection products of Chow classes over a locally Dedekind base

The intersection product `α · β = Δ!(α × β)` on total Chow
homology of schemes locally of finite type over a smooth scheme `X` over a
locally Dedekind base, together with associativity after the fiber-product
associator.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Dedekind

/-- The diagonal morphism of a scheme over a base, as a morphism in `Over S`. -/
noncomputable abbrev diagonal {S : Scheme.{u}} (X : Over S) : X ⟶ X ⨯ X :=
  prod.lift (𝟙 X) (𝟙 X)

/-- The Over-diagonal is the transport of `pullback.diagonal` along `prodLeftIsoPullback`. -/
theorem diagonal_left_eq {S : Scheme.{u}} (X : Over S) :
    (diagonal X).left =
      pullback.diagonal X.hom ≫ (Over.prodLeftIsoPullback X X).inv := sorry

/-- The Over-diagonal is an immersion. -/
instance diagonal_isImmersion {S : Scheme.{u}} (X : Over S)
    [Smooth X.hom] :
    IsImmersion (diagonal X).left := sorry

/-- The Over-diagonal of a smooth morphism is a regular immersion. -/
instance diagonal_isRegularImmersion {S : Scheme.{u}} (X : Over S)
    [Smooth X.hom] :
    IsRegularImmersion (diagonal X).left := sorry

/-- The fiber product of two schemes locally of finite type over `S` remains locally of
finite type over `S`. -/
instance pullback_locallyOfFiniteType {S : Scheme.{u}} {X Y Z : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom] :
    LocallyOfFiniteType (pullback fY fZ).hom := sorry

/-- The product of two locally finite-type morphisms over `S` is locally of finite type. -/
instance prodMap_locallyOfFiniteType {S : Scheme.{u}} {X Y Z : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left] :
    LocallyOfFiniteType (prod.map fY fZ).left := sorry

/-- Closed-specialization data for the coborder factorization of the Over-diagonal. -/
abbrev DiagonalSpecialization {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S)
    [LocallyOfFiniteType X.hom] [IsRegularImmersion (diagonal X).left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left) :=
  ClosedDeformation X.hom
    ((diagonal X).left.coborderRange.ι ≫ (X ⨯ X).hom)
    (diagonal X).left.liftCoborder
    (factorization_over X.hom (X ⨯ X).hom (diagonal X).left (diagonal X).w
      (diagonal X).left.liftCoborder (diagonal X).left.coborderRange.ι
      (diagonal X).left.liftCoborder_ι)
    (BivariantClass.normalSheafBundle (diagonal X).left e).toCoborder

/-- `DiagonalSpecialization` records a closed immersion followed by an open immersion. -/
theorem DiagonalSpecialization_spec {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S)
    [LocallyOfFiniteType X.hom] [IsRegularImmersion (diagonal X).left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) :
    IsClosedImmersion (diagonal X).left.liftCoborder ∧
      IsOpenImmersion (diagonal X).left.coborderRange.ι := sorry

/-- The canonical degree-`r` Gysin class of the Over-diagonal, obtained from the regular
immersion Gysin class of `diagonal X` after coborder factorization. -/
@[expose] noncomputable def diagonalGysinClass {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S)
    [LocallyOfFiniteType X.hom] [IsRegularImmersion (diagonal X).left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (r : ℕ) :
    BivariantClass δ (diagonal X) (r : ℤ) :=
  BivariantClass.overHom_eq_over (diagonal X) ▸
    BivariantClass.coborder_factorization (diagonal X) ▸
      BivariantClass.gysin_open_degree r ▸
        BivariantClass.gysinImmersion δ (diagonal X) e D r

/-- `diagonalGysinClass` is the coborder Gysin class of the Over-diagonal, transported
along the coborder factorization and the Over-hom comparison. -/
theorem diagonalGysinClass_def {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S)
    [LocallyOfFiniteType X.hom] [IsRegularImmersion (diagonal X).left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (r : ℕ) :
    diagonalGysinClass δ X e D r =
      BivariantClass.overHom_eq_over (diagonal X) ▸
        BivariantClass.coborder_factorization (diagonal X) ▸
          BivariantClass.gysin_open_degree r ▸
            BivariantClass.gysinImmersion δ (diagonal X) e D r := sorry

/-- The structure morphism of a fiber product over `X` to the base object `X`. -/
noncomputable abbrev fiberProductToBase {S : Scheme.{u}} {X Y Z : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) :
    pullback fY fZ ⟶ X :=
  pullback.fst fY fZ ≫ fY

/-- The comparison from a fiber product over `X` to the product over `S`. -/
noncomputable abbrev fiberProductToProduct {S : Scheme.{u}} {X Y Z : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) :
    pullback fY fZ ⟶ Y ⨯ Z :=
  prod.lift (pullback.fst fY fZ) (pullback.snd fY fZ)

/-- The comparison square identifying `Y ×_X Z` with the pullback of the diagonal
along `Y ×_S Z ⟶ X ×_S X`. -/
theorem intersectionSquare_isPullback {S : Scheme.{u}} {X Y Z : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) :
    IsPullback (fiberProductToBase fY fZ).left (fiberProductToProduct fY fZ).left
      (diagonal X).left (prod.map fY fZ).left := sorry

/-- For a smooth scheme with conormal sheaf of constant rank `r`, the intersection
product caps the Dedekind exterior product with the degree-`r` diagonal Gysin class. -/
@[expose] noncomputable def intersectionProduct {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (alpha : Total δ Y) (beta : Total δ Z) :
    Total δ (pullback fY fZ) :=
  Total.cap δ (diagonalGysinClass δ X e D r)
    (fiberProductToBase fY fZ) (fiberProductToProduct fY fZ) (prod.map fY fZ)
    (intersectionSquare_isPullback fY fZ)
    (Total.exteriorProduct δ h_delta Y Z alpha beta)

/-- The intersection product is the total cap of the Dedekind exterior product by the
canonical diagonal Gysin class. -/
theorem intersectionProduct_def {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (alpha : Total δ Y) (beta : Total δ Z) :
    intersectionProduct δ h_delta fY fZ e D r alpha beta =
      Total.cap δ (diagonalGysinClass δ X e D r)
        (fiberProductToBase fY fZ) (fiberProductToProduct fY fZ) (prod.map fY fZ)
        (intersectionSquare_isPullback fY fZ)
        (Total.exteriorProduct δ h_delta Y Z alpha beta) := sorry

/-- The intersection product of homogeneous classes is the degree-`n + m - 1 - r`
cap of their Dedekind exterior product. -/
theorem intersectionProduct_of {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (n m : ℤ)
    (alpha : RelativeChow δ Y n) (beta : RelativeChow δ Z m) :
    intersectionProduct δ h_delta fY fZ e D r
        (DirectSum.of (fun d : ℤ ↦ RelativeChow δ Y d) n alpha)
        (DirectSum.of (fun d : ℤ ↦ RelativeChow δ Z d) m beta) =
      DirectSum.of (fun d : ℤ ↦ RelativeChow δ (pullback fY fZ) d)
        (n + m - 1 - r)
        ((diagonalGysinClass δ X e D r).cap
          (fiberProductToBase fY fZ) (fiberProductToProduct fY fZ) (prod.map fY fZ)
          (intersectionSquare_isPullback fY fZ) (n + m - 1)
          (ExteriorProduct.pairing δ h_delta Y Z n m alpha beta)) := sorry

/-- The finite sum of diagonal Gysin coefficients acting on a homogeneous exterior
product. Relative point dimensions are nonnegative over the specified Dedekind
base, so coefficients beyond degree `n + m - 1` land in zero Chow groups. -/
private noncomputable def intersectionProductHomogeneous
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (n m : ℤ) :
    RelativeChow δ Y n →+ RelativeChow δ Z m →+ Total δ (pullback fY fZ) :=
  ∑ r ∈ Finset.range ((n + m - 1).toNat + 1),
    ((Total.cap δ (diagonalGysinClass δ X e D r)
        (fiberProductToBase fY fZ) (fiberProductToProduct fY fZ) (prod.map fY fZ)
        (intersectionSquare_isPullback fY fZ)).comp
      (DirectSum.of (fun d : ℤ ↦ RelativeChow δ (Y ⨯ Z) d) (n + m - 1))).compHom.comp
        (ExteriorProduct.pairing δ h_delta Y Z n m)

-- Visibility justification: the assembly uses the private finite-sum implementation
-- without adding that implementation to the public mathematical interface.
set_option backward.privateInPublic true in
/-- The intersection product on total relative Chow homology over a locally
Dedekind base, summing the diagonal Gysin coefficients in all relevant degrees. -/
noncomputable def intersectionProductTotal {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) :
    Total δ Y →+ Total δ Z →+ Total δ (pullback fY fZ) :=
  DirectSum.toAddMonoid fun n ↦
    AddMonoidHom.flip <| DirectSum.toAddMonoid fun m ↦
      AddMonoidHom.flip (intersectionProductHomogeneous δ h_delta fY fZ e D n m)

/-- On homogeneous classes, the total intersection product is the finite sum of
diagonal Gysin caps of their exterior product. -/
theorem intersectionProductTotal_of {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e)
    (n m : ℤ) (alpha : RelativeChow δ Y n) (beta : RelativeChow δ Z m) :
    intersectionProductTotal δ h_delta fY fZ e D
        (DirectSum.of (fun d : ℤ ↦ RelativeChow δ Y d) n alpha)
        (DirectSum.of (fun d : ℤ ↦ RelativeChow δ Z d) m beta) =
      ∑ r ∈ Finset.range ((n + m - 1).toNat + 1),
        Total.cap δ (diagonalGysinClass δ X e D r)
          (fiberProductToBase fY fZ) (fiberProductToProduct fY fZ) (prod.map fY fZ)
          (intersectionSquare_isPullback fY fZ)
          (DirectSum.of (fun d : ℤ ↦ RelativeChow δ (Y ⨯ Z) d) (n + m - 1)
            (ExteriorProduct.pairing δ h_delta Y Z n m alpha beta)) := sorry

/-- When the diagonal conormal sheaf has constant rank, the total intersection
product agrees with the product using that single Gysin coefficient. -/
theorem intersectionProductTotal_eq_intersectionProduct {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (alpha : Total δ Y) (beta : Total δ Z) :
    intersectionProductTotal δ h_delta fY fZ e D alpha beta =
      intersectionProduct δ h_delta fY fZ e D r alpha beta := sorry

/-- The total intersection product is independent of the normal-sheaf
identification and the deformation-to-the-normal-cone presentation. -/
theorem intersectionProductTotal_independent {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S}
    [LocallyOfFiniteType X.hom] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (fY : Y ⟶ X) (fZ : Z ⟶ X)
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e)
    (e' : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D' : DiagonalSpecialization δ X e') :
    intersectionProductTotal δ h_delta fY fZ e D =
      intersectionProductTotal δ h_delta fY fZ e' D' := sorry

/-- The canonical associator `(Y ×_X Z) ×_X W ≅ Y ×_X (Z ×_X W)`. -/
@[expose] noncomputable def fiberProductAssociator {S : Scheme.{u}} {X Y Z W : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) (fW : W ⟶ X) :
    pullback (pullback.fst fY fZ ≫ fY) fW ≅
      pullback fY (pullback.fst fZ fW ≫ fZ) :=
  pullback.congrHom
      (pullback.condition :
        pullback.fst fY fZ ≫ fY = pullback.snd fY fZ ≫ fZ)
      (rfl : fW = fW) ≪≫
    pullbackAssoc fY fZ fZ fW

/-- The fiber-product associator is proper on underlying schemes. -/
instance fiberProductAssociator_isProper {S : Scheme.{u}} {X Y Z W : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) (fW : W ⟶ X) :
    IsProper (fiberProductAssociator fY fZ fW).hom.left := sorry

/-- The first projection of the associator recovers the composite first projections. -/
theorem fiberProductAssociator_hom_fst {S : Scheme.{u}} {X Y Z W : Over S}
    (fY : Y ⟶ X) (fZ : Z ⟶ X) (fW : W ⟶ X) :
    (fiberProductAssociator fY fZ fW).hom ≫ pullback.fst fY (pullback.fst fZ fW ≫ fZ) =
      pullback.fst (pullback.fst fY fZ ≫ fY) fW ≫ pullback.fst fY fZ := sorry

/-- Over a locally Dedekind base, the intersection product of total Chow classes is
associative after pushforward along the fiber-product associator. -/
theorem intersectionProduct_assoc {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z W : Over S}
    [LocallyOfFiniteType X.hom] [Smooth X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType W.hom]
    (fY : Y ⟶ X) (fZ : Z ⟶ X) (fW : W ⟶ X)
    [LocallyOfFiniteType fY.left] [LocallyOfFiniteType fZ.left]
    [LocallyOfFiniteType fW.left]
    (e : Scheme.Modules.dual (normalSheaf (diagonal X).left) ≅
      conormalSheaf (diagonal X).left)
    (D : DiagonalSpecialization δ X e)
    (alpha : Total δ Y) (beta : Total δ Z) (gamma : Total δ W) :
    Total.map δ (fiberProductAssociator fY fZ fW).hom
        (intersectionProductTotal δ h_delta (fiberProductToBase fY fZ) fW e D
          (intersectionProductTotal δ h_delta fY fZ e D alpha beta) gamma) =
      intersectionProductTotal δ h_delta fY (fiberProductToBase fZ fW) e D alpha
        (intersectionProductTotal δ h_delta fZ fW e D beta gamma) := sorry

end AlgebraicGeometry.ChowGroup.Dedekind
