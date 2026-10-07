module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import stacks_project.Chap62.Remark_62_8_8_Functor

/-!
# Characteristic 2 affine-plane 0-cycle obstruction

This file records the geometry of `X = 𝔸²_k` over `S = Spec k` in characteristic
2, the canonical `σ`-invariant relative 0-cycle on `X ×_S X`, and the explicit
invariant subalgebra presenting `Sym²_S(X)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffinePlaneDegreeTwo

/-- The affine plane `X = 𝔸(2; Spec k)`. -/
abbrev plane (k : Type u) [Field k] : Scheme.{u} :=
  𝔸(ULift.{u} (Fin 2); Spec (.of k))

/-- The structure morphism `X ⟶ Spec k`. -/
abbrev planeHom (k : Type u) [Field k] : plane k ⟶ Spec (.of k) :=
  plane k ↘ Spec (.of k)

/-- The spectrum of a field is locally Noetherian. -/
instance instIsLocallyNoetherian_spec (k : Type u) [Field k] :
    IsLocallyNoetherian (Spec (.of k)) :=
  sorry

/-- The structure morphism of the affine plane is locally of finite type. -/
instance instLocallyOfFiniteType_planeHom (k : Type u) [Field k] :
    LocallyOfFiniteType (planeHom k) :=
  inferInstance

/-- The affine plane over a field is locally Noetherian. -/
instance instIsLocallyNoetherian_plane (k : Type u) [Field k] :
    IsLocallyNoetherian (plane k) :=
  LocallyOfFiniteType.isLocallyNoetherian (planeHom k)

/-- The fibre product `W = X ×_S X`. -/
abbrev square (k : Type u) [Field k] : Scheme.{u} :=
  pullback (planeHom k) (planeHom k)

/-- The first projection `W ⟶ X`. -/
abbrev fst (k : Type u) [Field k] : square k ⟶ plane k :=
  pullback.fst (planeHom k) (planeHom k)

/-- The second projection `W ⟶ X`. -/
abbrev snd (k : Type u) [Field k] : square k ⟶ plane k :=
  pullback.snd (planeHom k) (planeHom k)

/-- The structure morphism `W ⟶ Spec k`. -/
abbrev squareToBase (k : Type u) [Field k] : square k ⟶ Spec (.of k) :=
  snd k ≫ planeHom k

/-- The structure morphism of the affine square is locally of finite type. -/
instance instLocallyOfFiniteType_squareToBase (k : Type u) [Field k] :
    LocallyOfFiniteType (squareToBase k) :=
  inferInstance

/-- The affine square is locally Noetherian. -/
instance instIsLocallyNoetherian_square (k : Type u) [Field k] :
    IsLocallyNoetherian (square k) :=
  LocallyOfFiniteType.isLocallyNoetherian (squareToBase k)

/-- The generic-point coproduct of the affine square is quasi-compact. -/
instance instQuasiCompact_genericPoints_square (k : Type u) [Field k] :
    QuasiCompact (genericPointSpectrumCoproductTo (square k)) :=
  Scheme.Normalization.LocallyNoetherian.instGenericPointsQuasiCompact (square k)

/-- The generic-point coproduct of the affine square is quasi-separated. -/
instance instQuasiSeparated_genericPoints_square (k : Type u) [Field k] :
    QuasiSeparated (genericPointSpectrumCoproductTo (square k)) :=
  Scheme.Normalization.LocallyNoetherian.instGenericPointsQuasiSeparated (square k)

/-- The involution `σ : W ⟶ W` swapping the two factors. -/
abbrev involution (k : Type u) [Field k] : square k ⟶ square k :=
  (pullbackSymmetry (planeHom k) (planeHom k)).hom

/-- The `u`-coordinate on the affine plane. -/
def planeCoordU (k : Type u) [Field k] : Γ(plane k, ⊤) :=
  AffineSpace.coord (Spec (.of k)) (ULift.up (0 : Fin 2))

/-- The `v`-coordinate on the affine plane. -/
def planeCoordV (k : Type u) [Field k] : Γ(plane k, ⊤) :=
  AffineSpace.coord (Spec (.of k)) (ULift.up (1 : Fin 2))

/-- The total space `X_W = W ×_S X`. -/
abbrev totalOnSquare (k : Type u) [Field k] : Scheme.{u} :=
  pullback (planeHom k) (squareToBase k)

/-- The structure morphism `X_W ⟶ W`. -/
abbrev totalOnSquareHom (k : Type u) [Field k] : totalOnSquare k ⟶ square k :=
  pullback.snd (planeHom k) (squareToBase k)

/-- The projection `X_W ⟶ W` is locally of finite type. -/
instance instLocallyOfFiniteType_totalOnSquareHom (k : Type u) [Field k] :
    LocallyOfFiniteType (totalOnSquareHom k) :=
  inferInstance

/-- The section of `X_W ⟶ W` induced by the first projection `W ⟶ X`. -/
def firstSection (k : Type u) [Field k] : square k ⟶ totalOnSquare k :=
  pullback.lift (fst k) (𝟙 (square k)) sorry

/-- The section of `X_W ⟶ W` induced by the second projection `W ⟶ X`. -/
def secondSection (k : Type u) [Field k] : square k ⟶ totalOnSquare k :=
  pullback.lift (snd k) (𝟙 (square k)) sorry

/-- The first section is a section of `X_W ⟶ W`. -/
theorem firstSection_comp (k : Type u) [Field k] :
    firstSection k ≫ totalOnSquareHom k = 𝟙 (square k) :=
  sorry

/-- The second section is a section of `X_W ⟶ W`. -/
theorem secondSection_comp (k : Type u) [Field k] :
    secondSection k ≫ totalOnSquareHom k = 𝟙 (square k) :=
  sorry

/-- The point of the fibre of `X_W / W` over `w` selected by the first
projection. -/
def firstSectionFiberPoint (k : Type u) [Field k] (w : square k) :
    (totalOnSquareHom k).fiber w :=
  Scheme.Hom.Section.fiberPoint (totalOnSquareHom k) (firstSection k)
    (firstSection_comp k) w

/-- The point of the fibre of `X_W / W` over `w` selected by the second
projection. -/
def secondSectionFiberPoint (k : Type u) [Field k] (w : square k) :
    (totalOnSquareHom k).fiber w :=
  Scheme.Hom.Section.fiberPoint (totalOnSquareHom k) (secondSection k)
    (secondSection_comp k) w

/-- The first section point is 0-dimensional on the fibre. -/
theorem firstSectionFiberPoint_dimension (k : Type u) [Field k] (w : square k) :
    (totalOnSquareHom k).fiberDimensionFunction w (firstSectionFiberPoint k w) = 0 :=
  sorry

/-- The second section point is 0-dimensional on the fibre. -/
theorem secondSectionFiberPoint_dimension (k : Type u) [Field k] (w : square k) :
    (totalOnSquareHom k).fiberDimensionFunction w (secondSectionFiberPoint k w) = 0 :=
  sorry

/-- The canonical relative 0-cycle `α` on `X_W / W`, with `α_w = [x₁] + [x₂]`. -/
def canonicalPairCycle (k : Type u) [Field k] :
    RelativeCycle.Family (totalOnSquareHom k) 0 :=
  fun w ↦
    CycleGroup.point ((totalOnSquareHom k).fiberDimensionFunction w) 0
      (firstSectionFiberPoint k w) (firstSectionFiberPoint_dimension k w) +
    CycleGroup.point ((totalOnSquareHom k).fiberDimensionFunction w) 0
      (secondSectionFiberPoint k w) (secondSectionFiberPoint_dimension k w)

/-- Evaluating the canonical cycle recovers the sum of the two section points. -/
theorem canonicalPairCycle_eval (k : Type u) [Field k] (w : square k) :
    canonicalPairCycle k w =
      CycleGroup.point ((totalOnSquareHom k).fiberDimensionFunction w) 0
        (firstSectionFiberPoint k w) (firstSectionFiberPoint_dimension k w) +
      CycleGroup.point ((totalOnSquareHom k).fiberDimensionFunction w) 0
        (secondSectionFiberPoint k w) (secondSectionFiberPoint_dimension k w) :=
  sorry

/-- The canonical pair cycle is a relative 0-cycle. -/
theorem canonicalPairCycle_isRelative (k : Type u) [Field k] :
    RelativeCycle.IsRelative (canonicalPairCycle k) :=
  sorry

/-- The canonical pair cycle is fibrewise effective. -/
theorem canonicalPairCycle_isEffective (k : Type u) [Field k] :
    RelativeCycle.IsEffective (canonicalPairCycle k) :=
  sorry

/-- The polynomial ring `k[u₁, u₂, v₁, v₂]`. -/
abbrev coordRing (k : Type u) [CommRing k] : Type u :=
  MvPolynomial (ULift.{u} (Fin 4)) k

/-- The generator `u₁`. -/
def genU1 (k : Type u) [CommRing k] : coordRing k :=
  MvPolynomial.X (ULift.up (0 : Fin 4))

/-- The generator `u₂`. -/
def genU2 (k : Type u) [CommRing k] : coordRing k :=
  MvPolynomial.X (ULift.up (1 : Fin 4))

/-- The generator `v₁`. -/
def genV1 (k : Type u) [CommRing k] : coordRing k :=
  MvPolynomial.X (ULift.up (2 : Fin 4))

/-- The generator `v₂`. -/
def genV2 (k : Type u) [CommRing k] : coordRing k :=
  MvPolynomial.X (ULift.up (3 : Fin 4))

/-- The invariant subalgebra
`k[u₁+u₂, u₁u₂, v₁+v₂, v₁v₂, u₁v₁+u₂v₂] ⊂ k[u₁, u₂, v₁, v₂]`. -/
def invariantSubalgebra (k : Type u) [CommRing k] : Subalgebra k (coordRing k) :=
  Algebra.adjoin k
    {genU1 k + genU2 k, genU1 k * genU2 k, genV1 k + genV2 k, genV1 k * genV2 k,
      genU1 k * genV1 k + genU2 k * genV2 k}

/-- The five listed generators adjoin to the invariant subalgebra. -/
theorem invariantSubalgebra_adjoin (k : Type u) [CommRing k] :
    invariantSubalgebra k =
      Algebra.adjoin k
        {genU1 k + genU2 k, genU1 k * genU2 k, genV1 k + genV2 k,
          genV1 k * genV2 k, genU1 k * genV1 k + genU2 k * genV2 k} :=
  sorry

/-- The quotient scheme `Sym²_S(X)` as the spectrum of the invariant
subalgebra. -/
def symmetricSquare (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (.of (invariantSubalgebra k))

/-- The four coordinates on `W` as global sections, in the order
`u₁, u₂, v₁, v₂`. -/
def squareCoords (k : Type u) [Field k] (i : ULift.{u} (Fin 4)) :
    Γ(square k, ⊤) :=
  let n := i.down.val
  if n = 0 then (fst k).appTop (planeCoordU k)
  else if n = 1 then (snd k).appTop (planeCoordU k)
  else if n = 2 then (fst k).appTop (planeCoordV k)
  else (snd k).appTop (planeCoordV k)

/-- The comparison of `W` with affine 4-space over `Spec k`. -/
def squareToAffine4 (k : Type u) [Field k] :
    square k ⟶ 𝔸(ULift.{u} (Fin 4); Spec (.of k)) :=
  AffineSpace.homOfVector (squareToBase k) (squareCoords k)

/-- The comparison of `W` with `Spec(k[u₁, u₂, v₁, v₂])`. -/
def squareToSpecCoordRing (k : Type u) [Field k] :
    square k ⟶ Spec (.of (coordRing k)) :=
  squareToAffine4 k ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 4)) (.of k)).hom

/-- The quotient morphism `W ⟶ Sym²_S(X)` induced by the subalgebra
inclusion. -/
def toSymmetricSquare (k : Type u) [Field k] : square k ⟶ symmetricSquare k :=
  squareToSpecCoordRing k ≫
    Spec.map (CommRingCat.ofHom (algebraMap (invariantSubalgebra k) (coordRing k)))

/-- The structure morphism `Sym²_S(X) ⟶ Spec k`. -/
def symmetricSquareToBase (k : Type u) [Field k] :
    symmetricSquare k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (invariantSubalgebra k)))

/-- The symmetric square is locally Noetherian. -/
instance instIsLocallyNoetherian_symmetricSquare (k : Type u) [Field k] :
    IsLocallyNoetherian (symmetricSquare k) :=
  sorry

/-- The structure morphism of the symmetric square is locally of finite type. -/
instance instLocallyOfFiniteType_symmetricSquareToBase (k : Type u) [Field k] :
    LocallyOfFiniteType (symmetricSquareToBase k) :=
  sorry

/-- The quotient morphism `W ⟶ Sym²_S(X)` is locally of finite type. -/
instance instLocallyOfFiniteType_toSymmetricSquare (k : Type u) [Field k] :
    LocallyOfFiniteType (toSymmetricSquare k) :=
  sorry

/-- The morphism `W ⟶ Sym²_S(X)` lies over `Spec k`. -/
theorem toSymmetricSquare_comp (k : Type u) [Field k] :
    toSymmetricSquare k ≫ symmetricSquareToBase k = squareToBase k :=
  sorry

/-- The closed subscheme `V = Spec(k[u₁², v₁²])`, the image of the diagonal in
`Sym²_S(X)` in characteristic 2. -/
def diagonalSubalgebra (k : Type u) [CommRing k] : Subalgebra k (coordRing k) :=
  Algebra.adjoin k {genU1 k ^ 2, genV1 k ^ 2}

/-- The image of the diagonal as an affine scheme. -/
def diagonalImage (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (.of (diagonalSubalgebra k))

/-- Substitution of the diagonal `u₂ = u₁`, `v₂ = v₁` on the coordinate ring. -/
def diagonalSubstitution (k : Type u) [CommRing k] : coordRing k →ₐ[k] coordRing k :=
  MvPolynomial.aeval fun i : ULift.{u} (Fin 4) =>
    if i.down.val ≤ 1 then genU1 k else genV1 k

/-- Restriction of the invariant subalgebra along the diagonal substitution. -/
def invariantToDiagonal (k : Type u) [Field k] [CharP k 2] :
    invariantSubalgebra k →ₐ[k] diagonalSubalgebra k :=
  ((diagonalSubstitution k).comp (invariantSubalgebra k).val).codRestrict
    (diagonalSubalgebra k) sorry

/-- The closed immersion of the diagonal image into `Sym²_S(X)` in
characteristic 2. -/
def diagonalImageToSymmetricSquare (k : Type u) [Field k] [CharP k 2] :
    diagonalImage k ⟶ symmetricSquare k :=
  Spec.map (CommRingCat.ofHom (invariantToDiagonal k).toRingHom)

/-- The structure morphism of `W` is smooth. -/
instance instSmooth_squareToBase (k : Type u) [Field k] : Smooth (squareToBase k) :=
  sorry

/-- The affine square is a normal scheme. -/
theorem isNormal_square (k : Type u) [Field k] : (square k).isNormal :=
  sorry

/-- The affine square is weakly normal. -/
instance instWeaklyNormal_square (k : Type u) [Field k] :
    Scheme.WeaklyNormal (square k) :=
  sorry

/-- The symmetric square is a normal scheme. -/
theorem isNormal_symmetricSquare (k : Type u) [Field k] :
    (symmetricSquare k).isNormal :=
  sorry

/-- The associator identifying the nested pullback of `X` along
`W ⟶ Sym²_S(X)` with `X_W`. -/
def descentIso (k : Type u) [Field k] :
    pullback (pullback.snd (planeHom k) (symmetricSquareToBase k))
        (toSymmetricSquare k) ≅ totalOnSquare k :=
  RelativeCycle.pullbackSndAssocIso (planeHom k) (symmetricSquareToBase k)
      (toSymmetricSquare k) ≪≫
    pullback.congrHom rfl (toSymmetricSquare_comp k)

/-- The associator `descentIso` is a morphism over `W`. -/
theorem descentIso_hom_over (k : Type u) [Field k] :
    (descentIso k).hom ≫ totalOnSquareHom k =
      pullback.snd (pullback.snd (planeHom k) (symmetricSquareToBase k))
        (toSymmetricSquare k) :=
  sorry

end AlgebraicGeometry.AffinePlaneDegreeTwo

