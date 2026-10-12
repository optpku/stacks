/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import ReasLib.RingTheory.DividedPowers.DifferentialGraded.BaseChange.Unit

/-!
# Functoriality of divided-power chain-DGA base change

An algebra homomorphism `S →ₐ[R] T` acts on a scalar extension by applying it to the
coefficient of each pure tensor.  This file first packages that operation for arbitrary
tensor-product modules, then transports it through explicit divided-power chain-DGA
base-change models.  The resulting map is functorial in the coefficient algebra, compatible
with the scalar-extension unit, and characterized by its values on pure tensors.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe uR uS uT uU uM uA

namespace TensorProduct

variable {R : Type uR} {S : Type uS} {T : Type uT} {U : Type uU}
variable [CommSemiring R] [CommSemiring S] [CommSemiring T] [CommSemiring U]
variable [Algebra R S] [Algebra R T] [Algebra R U]
variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- The underlying `R`-linear map obtained by applying an `R`-algebra homomorphism to the
left coefficient of a tensor product. -/
def mapLeftAlgHomLinear (sigma : S →ₐ[R] T) :
    S ⊗[R] M →ₗ[R] T ⊗[R] M :=
  TensorProduct.map sigma.toLinearMap (LinearMap.id : M →ₗ[R] M)

/-- The underlying coefficient map carries the left scalar action through the algebra
homomorphism. -/
theorem mapLeftAlgHomLinear_smul (sigma : S →ₐ[R] T) (s : S) (z : S ⊗[R] M) :
    mapLeftAlgHomLinear sigma (s • z) =
      sigma s • mapLeftAlgHomLinear sigma z := sorry

/-- Tag 09PQ: applying an `R`-algebra homomorphism to the left coefficient defines a
semilinear map between scalar-extension tensor products. -/
@[stacks 09PQ "semilinear change of tensor coefficients"]
def mapLeftAlgHom (sigma : S →ₐ[R] T) :
    S ⊗[R] M →ₛₗ[sigma.toRingHom] T ⊗[R] M where
  toFun := mapLeftAlgHomLinear sigma
  map_add' := (mapLeftAlgHomLinear sigma).map_add
  map_smul' := mapLeftAlgHomLinear_smul sigma

/-- The semilinear coefficient map has the same underlying function as its `R`-linear
version. -/
@[simp]
theorem mapLeftAlgHom_apply (sigma : S →ₐ[R] T) (z : S ⊗[R] M) :
    mapLeftAlgHom sigma z = mapLeftAlgHomLinear sigma z := sorry

/-- Applying an algebra homomorphism to tensor coefficients acts on pure tensors by changing
only the left coefficient. -/
@[simp]
theorem mapLeftAlgHom_tmul (sigma : S →ₐ[R] T) (s : S) (m : M) :
    mapLeftAlgHom sigma (s ⊗ₜ[R] m) = sigma s ⊗ₜ[R] m := sorry

/-- Changing tensor coefficients along the identity algebra homomorphism is the identity. -/
@[simp]
theorem mapLeftAlgHom_id (z : S ⊗[R] M) :
    mapLeftAlgHom (AlgHom.id R S) z = z := sorry

/-- Successive changes of tensor coefficients agree with change along the composite algebra
homomorphism. -/
@[simp]
theorem mapLeftAlgHom_comp (sigma : S →ₐ[R] T) (tau : T →ₐ[R] U)
    (z : S ⊗[R] M) :
    mapLeftAlgHom (tau.comp sigma) z =
      mapLeftAlgHom tau (mapLeftAlgHom sigma z) := sorry

end TensorProduct

namespace DividedPowerChainAlgebra

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

namespace BaseChange

variable {A : DividedPowerChainAlgebra.{uR, uA} R}

/-- Transporting a natural-degree element through the two recorded tensor identifications
preserves addition. -/
theorem mapPiece_add (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℕ)
    (x y : X.algebra.toChainDGAlgebra.nonnegativePiece n) :
    Y.pieceIso n
        (TensorProduct.mapLeftAlgHom sigma ((X.pieceIso n).symm (x + y))) =
      Y.pieceIso n
          (TensorProduct.mapLeftAlgHom sigma ((X.pieceIso n).symm x)) +
        Y.pieceIso n
          (TensorProduct.mapLeftAlgHom sigma ((X.pieceIso n).symm y)) := sorry

/-- Transporting a natural-degree element through the two recorded tensor identifications is
semilinear along the coefficient algebra homomorphism. -/
theorem mapPiece_smul (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℕ) (s : S)
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece n) :
    Y.pieceIso n
        (TensorProduct.mapLeftAlgHom sigma ((X.pieceIso n).symm (s • x))) =
      sigma s • Y.pieceIso n
        (TensorProduct.mapLeftAlgHom sigma ((X.pieceIso n).symm x)) := sorry

/-- The canonical semilinear map between natural-degree pieces of two scalar-extension
models with different coefficient algebras. -/
@[stacks 09PQ "homogeneous map between scalar-extension models"]
def mapPiece (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℕ) :
    X.algebra.toChainDGAlgebra.nonnegativePiece n →ₛₗ[sigma.toRingHom]
      Y.algebra.toChainDGAlgebra.nonnegativePiece n where
  toFun := fun x ↦
    Y.pieceIso n
      (TensorProduct.mapLeftAlgHom sigma ((X.pieceIso n).symm x))
  map_add' := X.mapPiece_add sigma Y n
  map_smul' := X.mapPiece_smul sigma Y n

/-- Evaluation of the homogeneous base-change map is transport through the recorded tensor
identifications. -/
@[simp]
theorem mapPiece_apply (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece n) :
    X.mapPiece sigma Y n x =
      Y.pieceIso n
        (TensorProduct.mapLeftAlgHom sigma ((X.pieceIso n).symm x)) := sorry

/-- On a pure tensor, the homogeneous base-change map applies the algebra homomorphism to
the coefficient and leaves the original homogeneous element unchanged. -/
@[simp]
theorem mapPiece_tmul (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℕ) (s : S)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    X.mapPiece sigma Y n (X.pieceIso n (s ⊗ₜ[R] x)) =
      Y.pieceIso n (sigma s ⊗ₜ[R] x) := sorry

/-- The homogeneous base-change map preserves the chain-DGA unit. -/
@[simp]
theorem mapPiece_one (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) :
    X.mapPiece sigma Y 0 X.algebra.toChainDGAlgebra.one =
      Y.algebra.toChainDGAlgebra.one := sorry

/-- The homogeneous base-change maps preserve multiplication. -/
@[simp]
theorem mapPiece_mul (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n m : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece n)
    (y : X.algebra.toChainDGAlgebra.nonnegativePiece m) :
    X.mapPiece sigma Y (n + m)
        (X.algebra.toChainDGAlgebra.nonnegativeMul x y) =
      Y.algebra.toChainDGAlgebra.nonnegativeMul
        (X.mapPiece sigma Y n x) (X.mapPiece sigma Y m y) := sorry

/-- The homogeneous base-change maps commute with the differential from every positive
natural degree. -/
@[simp]
theorem mapPiece_d (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℕ+)
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece n) :
    Y.algebra.toChainDGAlgebra.nonnegativeDifferential n
        (X.mapPiece sigma Y n x) =
      X.mapPiece sigma Y ((n : ℕ) - 1)
        (X.algebra.toChainDGAlgebra.nonnegativeDifferential n x) := sorry

/-- The homogeneous base-change maps preserve divided powers on positive-even pieces. -/
@[simp]
theorem mapPiece_gammaPiece (X : BaseChange (R' := S) A)
    (sigma : S →ₐ[R] T) (Y : BaseChange (R' := T) A) (n d : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePiece (2 * (d + 1))) :
    Y.algebra.gamma.gammaPiece n d
        (X.mapPiece sigma Y (2 * (d + 1)) x) =
      X.mapPiece sigma Y (2 * (n * (d + 1)))
        (X.algebra.gamma.gammaPiece n d x) := sorry

/-- The degreewise coefficient-change map on all integer degrees.  Natural degrees use
`mapPiece`; negative degrees use the explicit zero map between the supported-zero pieces. -/
def degreeMap (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) : ∀ i : ℤ,
    X.algebra.toChainDGAlgebra.X i →ₛₗ[sigma.toRingHom]
      Y.algebra.toChainDGAlgebra.X i
  | .ofNat n => X.mapPiece sigma Y n
  | .negSucc _ => 0

/-- In a natural degree, the integer-graded coefficient-change map is `mapPiece`. -/
@[simp]
theorem degreeMap_ofNat (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℕ) :
    X.degreeMap sigma Y n = X.mapPiece sigma Y n := sorry

/-- In a negative degree, the integer-graded coefficient-change map is zero. -/
@[simp]
theorem degreeMap_negSucc (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℕ) :
    X.degreeMap sigma Y (.negSucc n) = 0 := sorry

/-- The integer-graded coefficient-change map has the expected pure-tensor formula in every
natural degree. -/
@[simp]
theorem degreeMap_tmul (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℕ) (s : S)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    X.degreeMap sigma Y n (X.pieceIso n (s ⊗ₜ[R] x)) =
      Y.pieceIso n (sigma s ⊗ₜ[R] x) := sorry

/-- The integer-graded coefficient-change map vanishes pointwise in every negative degree. -/
@[simp]
theorem degreeMap_apply_negSucc (X : BaseChange (R' := S) A)
    (sigma : S →ₐ[R] T) (Y : BaseChange (R' := T) A) (n : ℕ)
    (x : X.algebra.toChainDGAlgebra.X (.negSucc n)) :
    X.degreeMap sigma Y (.negSucc n) x = 0 := sorry

/-- The integer-graded coefficient-change maps commute with the chain differential. -/
theorem degreeMap_d (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℤ)
    (x : X.algebra.toChainDGAlgebra.X n) :
    X.degreeMap sigma Y (n - 1) (X.algebra.toChainDGAlgebra.d n x) =
      Y.algebra.toChainDGAlgebra.d n (X.degreeMap sigma Y n x) := sorry

/-- The integer-graded coefficient-change map preserves the homogeneous unit. -/
theorem degreeMap_one (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) :
    X.degreeMap sigma Y 0 X.algebra.toChainDGAlgebra.one =
      Y.algebra.toChainDGAlgebra.one := sorry

/-- The integer-graded coefficient-change maps preserve homogeneous multiplication. -/
theorem degreeMap_mul (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n m : ℤ)
    (x : X.algebra.toChainDGAlgebra.X n)
    (y : X.algebra.toChainDGAlgebra.X m) :
    X.degreeMap sigma Y (n + m)
        (X.algebra.toChainDGAlgebra.mul n m x y) =
      Y.algebra.toChainDGAlgebra.mul n m
        (X.degreeMap sigma Y n x) (X.degreeMap sigma Y m y) := sorry

/-- The underlying semilinear chain-DGA homomorphism obtained by changing the coefficient
algebra of an explicit base-change model. -/
def chainHom (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) :
    ChainDGAlgebra.SemilinearHom sigma.toRingHom
      X.algebra.toChainDGAlgebra Y.algebra.toChainDGAlgebra where
  map := X.degreeMap sigma Y
  map_d := X.degreeMap_d sigma Y
  map_one := X.degreeMap_one sigma Y
  map_mul := X.degreeMap_mul sigma Y

/-- The underlying semilinear chain-DGA homomorphism acts degreewise by `degreeMap`. -/
@[simp]
theorem chainHom_apply (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℤ)
    (x : X.algebra.toChainDGAlgebra.X n) :
    X.chainHom sigma Y n x = X.degreeMap sigma Y n x := sorry

/-- The underlying semilinear chain-DGA homomorphism preserves the total divided-power
operations. -/
theorem chainHom_map_gamma (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℕ)
    (x : X.algebra.toChainDGAlgebra.nonnegativePart.evenPositivePart) :
    Semilinear.evenMap (X.chainHom sigma Y) (X.algebra.gamma n x) =
      Y.algebra.gamma n
        (Semilinear.evenPositiveMap (X.chainHom sigma Y) x) := sorry

/-- Tag 09PQ: the canonical semilinear divided-power chain-DGA morphism obtained by applying
an `R`-algebra homomorphism to the coefficients of an explicit base-change model. -/
@[stacks 09PQ "map between divided-power chain-DGA base changes"]
def map (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) :
    SemilinearHom sigma.toRingHom X.algebra Y.algebra where
  toChainHom := X.chainHom sigma Y
  map_gamma := X.chainHom_map_gamma sigma Y

/-- The chain-DGA map underlying coefficient change is `chainHom`. -/
@[simp]
theorem map_toChainHom (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) :
    (X.map sigma Y).toChainHom = X.chainHom sigma Y := sorry

/-- The homogeneous component of coefficient change is `degreeMap`. -/
@[simp]
theorem map_component (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (i : ℤ) :
    (X.map sigma Y).toChainHom.map i = X.degreeMap sigma Y i := sorry

/-- The canonical base-change morphism acts degreewise by the explicit coefficient-change
map. -/
@[simp]
theorem map_apply (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (i : ℤ)
    (x : X.algebra.toChainDGAlgebra.X i) :
    X.map sigma Y i x = X.degreeMap sigma Y i x := sorry

/-- The canonical base-change morphism applies the algebra homomorphism to the coefficient of
every pure tensor. -/
@[simp]
theorem map_tmul (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (n : ℕ) (s : S)
    (x : A.toChainDGAlgebra.nonnegativePiece n) :
    X.map sigma Y n (X.pieceIso n (s ⊗ₜ[R] x)) =
      Y.pieceIso n (sigma s ⊗ₜ[R] x) := sorry

/-- The canonical base-change morphism vanishes in every negative degree. -/
@[simp]
theorem map_apply_negSucc (X : BaseChange (R' := S) A)
    (sigma : S →ₐ[R] T) (Y : BaseChange (R' := T) A) (n : ℕ)
    (x : X.algebra.toChainDGAlgebra.X (.negSucc n)) :
    X.map sigma Y (.negSucc n) x = 0 := sorry

/-- A semilinear divided-power map between base-change models agrees with coefficient change
when it has the expected value on every pure tensor. -/
def AgreesOnPureTensors (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A)
    (f : SemilinearHom sigma.toRingHom X.algebra Y.algebra) : Prop :=
  ∀ (n : ℕ) (s : S) (x : A.toChainDGAlgebra.nonnegativePiece n),
    f n (X.pieceIso n (s ⊗ₜ[R] x)) =
      Y.pieceIso n (sigma s ⊗ₜ[R] x)

/-- The canonical base-change morphism agrees with coefficient change on pure tensors. -/
theorem map_agreesOnPureTensors (X : BaseChange (R' := S) A)
    (sigma : S →ₐ[R] T) (Y : BaseChange (R' := T) A) :
    X.AgreesOnPureTensors sigma Y (X.map sigma Y) := sorry

/-- Semilinear divided-power maps between explicit base-change models are determined by their
values on pure tensors in natural degrees. -/
@[ext]
theorem hom_ext (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A)
    {f g : SemilinearHom sigma.toRingHom X.algebra Y.algebra}
    (h : ∀ (n : ℕ) (s : S) (x : A.toChainDGAlgebra.nonnegativePiece n),
      f n (X.pieceIso n (s ⊗ₜ[R] x)) =
        g n (X.pieceIso n (s ⊗ₜ[R] x))) :
    f = g := sorry

/-- A semilinear divided-power map with the coefficient-change formula is the canonical
base-change morphism. -/
theorem map_unique (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A)
    (f : SemilinearHom sigma.toRingHom X.algebra Y.algebra)
    (h : X.AgreesOnPureTensors sigma Y f) :
    f = X.map sigma Y := sorry

/-- Postcomposing the scalar-extension unit with coefficient change preserves addition. -/
theorem mapAfterUnit_add (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (i : ℤ)
    (x y : A.toChainDGAlgebra.X i) :
    X.map sigma Y i (X.unit i (x + y)) =
      X.map sigma Y i (X.unit i x) +
        X.map sigma Y i (X.unit i y) := sorry

/-- Postcomposing the scalar-extension unit with coefficient change is semilinear along
`algebraMap R T`. -/
theorem mapAfterUnit_smul (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (i : ℤ) (r : R)
    (x : A.toChainDGAlgebra.X i) :
    X.map sigma Y i (X.unit i (r • x)) =
      algebraMap R T r • X.map sigma Y i (X.unit i x) := sorry

/-- The degreewise semilinear map obtained by postcomposing the scalar-extension unit with
coefficient change. -/
def mapAfterUnit (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (i : ℤ) :
    A.toChainDGAlgebra.X i →ₛₗ[algebraMap R T]
      Y.algebra.toChainDGAlgebra.X i where
  toFun := fun x ↦ X.map sigma Y i (X.unit i x)
  map_add' := X.mapAfterUnit_add sigma Y i
  map_smul' := X.mapAfterUnit_smul sigma Y i

/-- Evaluation of `mapAfterUnit` is pointwise composition with the canonical coefficient-change
map. -/
@[simp]
theorem mapAfterUnit_apply (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (i : ℤ)
    (x : A.toChainDGAlgebra.X i) :
    X.mapAfterUnit sigma Y i x = X.map sigma Y i (X.unit i x) := sorry

/-- Bundled degreewise naturality of the scalar-extension unit under coefficient change. -/
@[simp]
theorem mapAfterUnit_eq_unitMap (X : BaseChange (R' := S) A)
    (sigma : S →ₐ[R] T) (Y : BaseChange (R' := T) A) (i : ℤ) :
    X.mapAfterUnit sigma Y i = Y.unitMap i := sorry

/-- Coefficient change carries the scalar-extension unit of the source model to that of the
target model. -/
@[simp]
theorem map_unit_apply (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (i : ℤ)
    (x : A.toChainDGAlgebra.X i) :
    X.map sigma Y i (X.unit i x) = Y.unit i x := sorry

/-- Coefficient change along the identity algebra homomorphism is the identity on a fixed
base-change model. -/
@[simp]
theorem map_id (X : BaseChange (R' := S) A) :
    X.map (AlgHom.id R S) X = SemilinearHom.id X.algebra := sorry

/-- Along the identity algebra homomorphism, coefficient change between two models is the
canonical comparison on every homogeneous piece. -/
@[simp]
theorem map_id_apply (X Y : BaseChange (R' := S) A) (i : ℤ)
    (x : X.algebra.toChainDGAlgebra.X i) :
    X.map (AlgHom.id R S) Y i x =
      (X.chainComparison Y).toChainHom i x := sorry

section Composition

variable {U : Type uU} [CommRing U] [Algebra R U]

/-- Coefficient change is functorial in the coefficient algebra. -/
@[simp]
theorem map_comp (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (tau : T →ₐ[R] U)
    (Z : BaseChange (R' := U) A) :
    X.map (tau.comp sigma) Z =
      SemilinearHom.comp (Y.map tau Z) (X.map sigma Y) := sorry

/-- Functoriality of coefficient change evaluated on a homogeneous element. -/
@[simp]
theorem map_comp_apply (X : BaseChange (R' := S) A) (sigma : S →ₐ[R] T)
    (Y : BaseChange (R' := T) A) (tau : T →ₐ[R] U)
    (Z : BaseChange (R' := U) A) (i : ℤ)
    (x : X.algebra.toChainDGAlgebra.X i) :
    X.map (tau.comp sigma) Z i x =
      Y.map tau Z i (X.map sigma Y i x) := sorry

end Composition

end BaseChange

end DividedPowerChainAlgebra
