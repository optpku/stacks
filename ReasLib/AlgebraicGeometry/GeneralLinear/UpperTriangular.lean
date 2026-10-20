module

public import Mathlib.LinearAlgebra.Matrix.Reindex
public import ReasLib.AlgebraicGeometry.GeneralLinear.GroupScheme
public import ReasLib.AlgebraicGeometry.GeneralLinear.Two
public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup.Factorization
public import ReasLib.RingTheory.Sequence.Koszul.Regularity.UpperTriangular

/-!
# The upper-triangular subgroup of `GL₂`

This file constructs the upper-triangular subgroup scheme of `GL₂`, its group structure, and
its closed inclusion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GLTwo.UpperTriangular

/-- The lower-left entry of an upper-triangular identity matrix is zero. -/
theorem one_lowerLeft {A : Type u} [CommRing A] :
    (1 : Matrix.GeneralLinearGroup (GLTwo.index) A) (ULift.up 1) (ULift.up 0) = 0 := sorry

/-- Upper-triangular invertible matrices are closed under multiplication. -/
theorem mul_lowerLeft {A : Type u} [CommRing A]
    {M N : Matrix.GeneralLinearGroup (GLTwo.index) A}
    (hM : M (ULift.up 1) (ULift.up 0) = 0)
    (hN : N (ULift.up 1) (ULift.up 0) = 0) :
    (M * N) (ULift.up 1) (ULift.up 0) = 0 := sorry

/-- The inverse of an upper-triangular invertible matrix is upper triangular. -/
theorem inv_lowerLeft {A : Type u} [CommRing A]
    {M : Matrix.GeneralLinearGroup (GLTwo.index) A}
    (hM : M (ULift.up 1) (ULift.up 0) = 0) :
    M⁻¹ (ULift.up 1) (ULift.up 0) = 0 := sorry

/-- The subgroup of invertible `2 × 2` matrices with zero lower-left entry. -/
def points (A : Type u) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (GLTwo.index) A) where
  carrier := { M | M (ULift.up 1) (ULift.up 0) = 0 }
  one_mem' := one_lowerLeft
  mul_mem' := mul_lowerLeft
  inv_mem' := inv_lowerLeft

/-- Membership in `points A` is upper triangularity of the represented matrix. -/
theorem mem_points {A : Type u} [CommRing A]
    (M : Matrix.GeneralLinearGroup (GLTwo.index) A) :
    M ∈ points A ↔ M (ULift.up 1) (ULift.up 0) = 0 := sorry

/-- The coordinate ring of the rank-two upper-triangular group scheme. -/
abbrev coordinateRing (k : Type u) [CommRing k] : Type u :=
  RingTheory.Sequence.UpperTriangular.Ring k 2

/-- The universal upper-triangular matrix, reindexed by `GLTwo.index`. -/
def rawUniversalMatrix (k : Type u) [CommRing k] :
  Matrix (GLTwo.index) (GLTwo.index) (coordinateRing k) :=
  Matrix.reindex (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2).symm
      (Equiv.ulift : ULift.{u} (Fin 2) ≃ Fin 2).symm
    (RingTheory.Sequence.UpperTriangular.matrix :
      Matrix (Fin 2) (Fin 2) (coordinateRing k))

/-- Entries of `rawUniversalMatrix` are the reindexed universal upper-triangular entries. -/
theorem rawUniversalMatrix_apply (k : Type u) [CommRing k] (i j : Fin 2) :
    rawUniversalMatrix k (ULift.up i) (ULift.up j) =
      (RingTheory.Sequence.UpperTriangular.matrix :
        Matrix (Fin 2) (Fin 2) (coordinateRing k)) i j := sorry

/-- The determinant of the universal upper-triangular matrix is a unit. -/
theorem rawUniversalMatrix_det_isUnit (k : Type u) [CommRing k] :
    IsUnit (Matrix.det (rawUniversalMatrix k)) := sorry

/-- The universal upper-triangular matrix as an invertible matrix. -/
def universalMatrix (k : Type u) [CommRing k] :
    Matrix.GeneralLinearGroup (GLTwo.index) (coordinateRing k) :=
  Matrix.GeneralLinearGroup.mk'' (rawUniversalMatrix k)
    (rawUniversalMatrix_det_isUnit k)

/-- The lower-left entry of the universal upper-triangular matrix is zero. -/
theorem universalMatrix_lowerLeft (k : Type u) [CommRing k] :
    universalMatrix k (ULift.up 1) (ULift.up 0) = 0 := sorry

/-- The coordinate-ring map defining the closed inclusion into `GL₂`. -/
def inclusionRingHom (k : Type u) [CommRing k] :
    GLTwo.coordinateRing k →+* coordinateRing k :=
  GeneralLinear.CoordinateRing.homOfMatrix (GLTwo.index)
    (algebraMap k (coordinateRing k)) (universalMatrix k)

/-- The inclusion coordinate-ring map respects the maps from the base ring. -/
theorem inclusionRingHom_comp_algebraMap (k : Type u) [CommRing k] :
    (inclusionRingHom k).comp (algebraMap k (GLTwo.coordinateRing k)) =
      algebraMap k (coordinateRing k) := sorry

/-- The upper-triangular scheme over `Spec(k)`. -/
abbrev schemeOver (k : Type u) [CommRing k] : Over (Spec (CommRingCat.of k)) :=
  Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap k (coordinateRing k)))

/-- The underlying scheme of `schemeOver k` is the spectrum of its coordinate ring. -/
theorem schemeOver_left (k : Type u) [CommRing k] :
    (schemeOver k).left = Spec (CommRingCat.of (coordinateRing k)) := sorry

/-- The structure morphism of `schemeOver k` is induced by its `k`-algebra structure. -/
theorem schemeOver_hom (k : Type u) [CommRing k] :
    (schemeOver k).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (coordinateRing k))) := sorry

/-- The spectrum map of the inclusion ring map respects the structure morphisms. -/
theorem inclusion_over (k : Type u) [CommRing k] :
    Spec.map (CommRingCat.ofHom (inclusionRingHom k)) ≫
        (GeneralLinear.schemeOver k (GLTwo.index)).hom =
      (schemeOver k).hom := sorry

/-- The closed immersion of the upper-triangular scheme into `GL₂`. -/
def inclusion (k : Type u) [CommRing k] :
    schemeOver k ⟶ GeneralLinear.schemeOver k (GLTwo.index) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (inclusionRingHom k))) (inclusion_over k)

/-- The inclusion evaluates to the universal upper-triangular matrix. -/
theorem inclusion_matrix (k : Type u) [CommRing k] :
    GeneralLinear.HomOver.matrixOfHom (GLTwo.index) (inclusion k) =
      Matrix.GeneralLinearGroup.map
        (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing k))).inv.hom
        (universalMatrix k) := sorry

/-- The upper-triangular inclusion is a closed immersion. -/
instance inclusion_isClosedImmersion (k : Type u) [CommRing k] :
    IsClosedImmersion (inclusion k).left := sorry

/-- The upper-triangular inclusion is a monomorphism in the slice category. -/
instance inclusion_mono (k : Type u) [CommRing k] : Mono (inclusion k) := sorry

/-- Polynomial evaluation at an upper-triangular invertible matrix. -/
def polynomialEval {A : Type u} [CommRing A] (k : Type u) [CommRing k]
    (φ : k →+* A) (M : Matrix.GeneralLinearGroup (GLTwo.index) A) :
    MvPolynomial (RingTheory.Sequence.UpperTriangular.Index 2) k →+* A :=
  MvPolynomial.eval₂Hom φ fun ij ↦ M (ULift.up ij.1.1) (ULift.up ij.1.2)

/-- Polynomial evaluation sends the upper-triangular denominator to a unit. -/
theorem polynomialEval_denominator_isUnit {A : Type u} [CommRing A]
    (k : Type u) [CommRing k] (φ : k →+* A)
    (M : Matrix.GeneralLinearGroup (GLTwo.index) A)
    (hM : M (ULift.up 1) (ULift.up 0) = 0) :
    IsUnit (polynomialEval k φ M
      (∏ i : Fin 2, (MvPolynomial.X ⟨(i, i), le_rfl⟩ :
        MvPolynomial (RingTheory.Sequence.UpperTriangular.Index 2) k))) := sorry

/-- The coordinate-ring map classified by an upper-triangular invertible matrix. -/
def coordinateRingHom {A : Type u} [CommRing A] (k : Type u) [CommRing k]
    (φ : k →+* A) (M : Matrix.GeneralLinearGroup (GLTwo.index) A)
    (hM : M (ULift.up 1) (ULift.up 0) = 0) : coordinateRing k →+* A :=
  IsLocalization.Away.lift
    (∏ i : Fin 2, (MvPolynomial.X ⟨(i, i), le_rfl⟩ :
      MvPolynomial (RingTheory.Sequence.UpperTriangular.Index 2) k))
    (polynomialEval_denominator_isUnit k φ M hM)

/-- The classified coordinate-ring map extends polynomial evaluation. -/
theorem coordinateRingHom_comp_algebraMap {A : Type u} [CommRing A]
    (k : Type u) [CommRing k] (φ : k →+* A)
    (M : Matrix.GeneralLinearGroup (GLTwo.index) A)
    (hM : M (ULift.up 1) (ULift.up 0) = 0) :
    (coordinateRingHom k φ M hM).comp
        (algebraMap (MvPolynomial (RingTheory.Sequence.UpperTriangular.Index 2) k)
          (coordinateRing k)) = polynomialEval k φ M := sorry

/-- The classified coordinate-ring map restricts to the prescribed map on `k`. -/
theorem coordinateRingHom_comp_base {A : Type u} [CommRing A]
    (k : Type u) [CommRing k] (φ : k →+* A)
    (M : Matrix.GeneralLinearGroup (GLTwo.index) A)
    (hM : M (ULift.up 1) (ULift.up 0) = 0) :
    (coordinateRingHom k φ M hM).comp (algebraMap k (coordinateRing k)) = φ := sorry

/-- The coordinate-ring map of an upper-triangular generalized point is compatible with the
base map. -/
theorem compatibleRingHom_w (k : Type u) [CommRing k]
    {T : Over (Spec (CommRingCat.of k))}
    (M : Matrix.GeneralLinearGroup (GLTwo.index) Γ(T.left, ⊤))
    (hM : M (ULift.up 1) (ULift.up 0) = 0) :
    CommRingCat.ofHom (algebraMap k (coordinateRing k)) ≫
        CommRingCat.ofHom
          (coordinateRingHom k (Scheme.OverSpec.baseRingHom T).hom M hM) =
      Scheme.OverSpec.baseRingHom T := sorry

/-- The compatible ring map associated to an upper-triangular matrix-valued point. -/
def compatibleRingHom (k : Type u) [CommRing k]
    {T : Over (Spec (CommRingCat.of k))}
    (M : Matrix.GeneralLinearGroup (GLTwo.index) Γ(T.left, ⊤))
    (hM : M (ULift.up 1) (ULift.up 0) = 0) :
    Scheme.OverSpec.CompatibleRingHom
      (CommRingCat.ofHom (algebraMap k (coordinateRing k))) T :=
  Under.homMk
    (CommRingCat.ofHom
      (coordinateRingHom k (Scheme.OverSpec.baseRingHom T).hom M hM))
    (compatibleRingHom_w k M hM)

/-- The upper-triangular scheme point classified by an upper-triangular matrix. -/
def ofMatrix (k : Type u) [CommRing k] {T : Over (Spec (CommRingCat.of k))}
    (M : Matrix.GeneralLinearGroup (GLTwo.index) Γ(T.left, ⊤))
    (hM : M (ULift.up 1) (ULift.up 0) = 0) : T ⟶ schemeOver k :=
  Scheme.OverSpec.homOfRingHom
    (CommRingCat.ofHom (algebraMap k (coordinateRing k))) (compatibleRingHom k M hM)

/-- Classification by `ofMatrix` followed by inclusion recovers the given matrix-valued point. -/
theorem ofMatrix_inclusion (k : Type u) [CommRing k]
    {T : Over (Spec (CommRingCat.of k))}
    (M : Matrix.GeneralLinearGroup (GLTwo.index) Γ(T.left, ⊤))
    (hM : M (ULift.up 1) (ULift.up 0) = 0) :
    ofMatrix k M hM ≫ inclusion k =
      GeneralLinear.HomOver.ofMatrix (GLTwo.index) M := sorry

/-- Every generalized point of the upper-triangular scheme has upper-triangular image in `GL₂`. -/
theorem matrixOfHom_inclusion_lowerLeft (k : Type u) [CommRing k]
    {T : Over (Spec (CommRingCat.of k))} (f : T ⟶ schemeOver k) :
    GeneralLinear.HomOver.matrixOfHom (GLTwo.index) (f ≫ inclusion k)
        (ULift.up 1) (ULift.up 0) = 0 := sorry

/-- The identity generalized point of `GL₂` is upper triangular. -/
theorem onePoint_lowerLeft (k : Type u) [CommRing k] :
    (1 : Matrix.GeneralLinearGroup (GLTwo.index)
      Γ((𝟙_ (Over (Spec (CommRingCat.of.{u} k)))).left, ⊤))
        (ULift.up 1) (ULift.up 0) = 0 := sorry

/-- The identity map factored through the upper-triangular scheme. -/
def one (k : Type u) [CommRing k] :
    𝟙_ (Over (Spec (CommRingCat.of.{u} k))) ⟶ schemeOver k :=
  ofMatrix.{u, u} k
    (1 : Matrix.GeneralLinearGroup (GLTwo.index)
      Γ((𝟙_ (Over (Spec (CommRingCat.of.{u} k)))).left, ⊤))
    (onePoint_lowerLeft k)

/-- The matrix product of the two upper-triangular projections. -/
def mulMatrix (k : Type u) [CommRing k] :
    Matrix.GeneralLinearGroup (GLTwo.index)
      Γ((schemeOver k ⊗ schemeOver k).left, ⊤) :=
  GeneralLinear.HomOver.matrixOfHom (GLTwo.index)
      (fst (schemeOver k) (schemeOver k) ≫ inclusion k) *
    GeneralLinear.HomOver.matrixOfHom (GLTwo.index)
      (snd (schemeOver k) (schemeOver k) ≫ inclusion k)

/-- The product matrix of the two projections remains upper triangular. -/
theorem mulMatrix_lowerLeft (k : Type u) [CommRing k] :
    mulMatrix k (ULift.up 1) (ULift.up 0) = 0 := sorry

/-- Multiplication on the upper-triangular scheme. -/
def mul (k : Type u) [CommRing k] : schemeOver k ⊗ schemeOver k ⟶ schemeOver k :=
  ofMatrix k (mulMatrix k) (mulMatrix_lowerLeft k)

/-- The inverse matrix of the universal upper-triangular point. -/
def invMatrix (k : Type u) [CommRing k] :
    Matrix.GeneralLinearGroup (GLTwo.index) Γ((schemeOver k).left, ⊤) :=
  (GeneralLinear.HomOver.matrixOfHom (GLTwo.index) (inclusion k))⁻¹

/-- The inverse matrix of the universal upper-triangular point remains upper triangular. -/
theorem invMatrix_lowerLeft (k : Type u) [CommRing k] :
    invMatrix k (ULift.up 1) (ULift.up 0) = 0 := sorry

/-- Inversion on the upper-triangular scheme. -/
def inv (k : Type u) [CommRing k] : schemeOver k ⟶ schemeOver k :=
  ofMatrix k (invMatrix k) (invMatrix_lowerLeft k)

/-- The factored identity agrees with the identity of `GL₂`. -/
theorem one_inclusion (k : Type u) [CommRing k] :
    one k ≫ inclusion k = η[GeneralLinear.schemeOver k (GLTwo.index)] := sorry

/-- The factored multiplication agrees with multiplication in `GL₂`. -/
theorem mul_inclusion (k : Type u) [CommRing k] :
    mul k ≫ inclusion k =
      (inclusion k ⊗ₘ inclusion k) ≫ μ[GeneralLinear.schemeOver k (GLTwo.index)] := sorry

/-- The factored inverse agrees with inversion in `GL₂`. -/
theorem inv_inclusion (k : Type u) [CommRing k] :
    inv k ≫ inclusion k =
      inclusion k ≫ ι[GeneralLinear.schemeOver k (GLTwo.index)] := sorry

/-- The explicit factorization of the `GL₂` operations through the upper-triangular scheme. -/
def factorization (k : Type u) [CommRing k] :
    CategoryTheory.GrpObj.Factorization (inclusion k) where
  one := one k
  mul := mul k
  inv := inv k
  one_hom := one_inclusion k
  mul_hom := mul_inclusion k
  inv_hom := inv_inclusion k

/-- The canonical group-object structure on the upper-triangular scheme. -/
instance instGrpObjSchemeOver (k : Type u) [CommRing k] : GrpObj (schemeOver k) :=
  (factorization k).toGrpObj

/-- The upper-triangular inclusion is a morphism of group objects. -/
instance inclusion_isMonHom (k : Type u) [CommRing k] : IsMonHom (inclusion k) := sorry

/-- The rank-two upper-triangular group scheme. -/
def groupScheme (k : Type u) [CommRing k] : Grp (Over (Spec (CommRingCat.of k))) :=
  { X := schemeOver k }

/-- The underlying object of the upper-triangular group scheme is `schemeOver k`. -/
theorem groupScheme_X (k : Type u) [CommRing k] : (groupScheme k).X = schemeOver k := sorry

/-- The upper-triangular group scheme as a closed subgroup of `GL₂`. -/
def closedSubgroup (k : Type u) [CommRing k] :
    Scheme.ClosedSubgroup (GeneralLinear.schemeOver k (GLTwo.index)) :=
  Scheme.ClosedSubgroup.mk (inclusion k)

/-- The underlying morphism of `closedSubgroup k` is the explicit inclusion. -/
theorem closedSubgroup_inclusion (k : Type u) [CommRing k] :
    (closedSubgroup k).hom.hom.hom = inclusion k := sorry

end AlgebraicGeometry.GLTwo.UpperTriangular
