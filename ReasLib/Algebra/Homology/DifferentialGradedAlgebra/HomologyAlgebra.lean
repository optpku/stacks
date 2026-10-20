module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.Algebra.DirectSum.NonnegGradedAlgebra.Hom
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Nonnegative

/-!
# The graded algebra on homology of a chain DGA

This file equips the canonical Mathlib homology modules of a strictly commutative chain DGA with
their nonnegative graded-algebra structure. Multiplication is defined by choosing cycle
representatives and then multiplying them; the public class formula makes the result independent
of that implementation choice.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DirectSum

universe u v

namespace ChainDGAlgebra

variable {R : Type u} [CommRing R]

/-- The degree-`n` canonical homology module of a chain DGA, restricted to natural degrees. -/
abbrev homologyPiece (A : ChainDGAlgebra.{u, v} R) (n : ℕ) : Type v :=
  A.homology (n : ℤ)

set_option backward.privateInPublic true in
/-- An implementation-only choice of a cycle representing a canonical homology class. -/
private def homologyCycleRepresentative (A : ChainDGAlgebra.{u, v} R) (n : ℕ) :
    A.homologyPiece n → A.cycles (n : ℤ) :=
  Function.surjInv <|
    (ModuleCat.epi_iff_surjective (A.homologyπ (n : ℤ))).mp inferInstance

/-- The selected cycle represents the homology class from which it was chosen. -/
private theorem homologyCycleRepresentative_spec (A : ChainDGAlgebra.{u, v} R) (n : ℕ)
    (x : A.homologyPiece n) :
    A.homologyπ n (A.homologyCycleRepresentative n x) = x := sorry

/-- The successor selected by the chain-complex shape lowers a natural degree by one. -/
theorem down_next_ofNat (n : ℕ) :
    (ComplexShape.down ℤ).next (n : ℤ) = (n : ℤ) - 1 := sorry

/-- The product of two cycles in natural degrees is again a cycle. -/
theorem d_nonnegativeMul_cycles_eq_zero (A : ChainDGAlgebra.{u, v} R) (n m : ℕ)
    (x : A.cycles (n : ℤ)) (y : A.cycles (m : ℤ)) :
    ((forget₂ (ModuleCat.{v} R) Ab).map
      (A.toChainComplex.d (n + m) ((n + m : ℕ) - 1)))
        (A.nonnegativeMul (A.iCycles n x) (A.iCycles m y)) = 0 := sorry

/-- Multiplication of cycles, with the result bundled in the canonical cycle object. -/
def cyclesMul (A : ChainDGAlgebra.{u, v} R) (n m : ℕ)
    (x : A.cycles (n : ℤ)) (y : A.cycles (m : ℤ)) :
    A.cycles ((n + m : ℕ) : ℤ) :=
  A.toChainComplex.cyclesMk
    (A.nonnegativeMul (A.iCycles n x) (A.iCycles m y)) ((n + m : ℕ) - 1)
      (down_next_ofNat (n + m))
      (A.d_nonnegativeMul_cycles_eq_zero n m x y)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The underlying value of multiplication on canonical homology classes. -/
def homologyMulValue (A : ChainDGAlgebra.{u, v} R) (n m : ℕ)
    (x : A.homologyPiece n) (y : A.homologyPiece m) : A.homologyPiece (n + m) :=
  A.homologyπ (n + m) <| A.cyclesMul n m
    (homologyCycleRepresentative A n x) (homologyCycleRepresentative A m y)

/-- Homology multiplication is additive in its right input. -/
theorem homologyMulValue_add_right (A : ChainDGAlgebra.{u, v} R) (n m : ℕ)
    (x : A.homologyPiece n) (y z : A.homologyPiece m) :
    A.homologyMulValue n m x (y + z) =
      A.homologyMulValue n m x y + A.homologyMulValue n m x z := sorry

/-- Homology multiplication is linear in its right input. -/
theorem homologyMulValue_smul_right (A : ChainDGAlgebra.{u, v} R) (n m : ℕ)
    (r : R) (x : A.homologyPiece n) (y : A.homologyPiece m) :
    A.homologyMulValue n m x (r • y) =
      (RingHom.id R) r • A.homologyMulValue n m x y := sorry

/-- Multiplication by a fixed homology class as a linear map in the right input. -/
def homologyMulRight (A : ChainDGAlgebra.{u, v} R) (n m : ℕ) (x : A.homologyPiece n) :
    A.homologyPiece m →ₗ[R] A.homologyPiece (n + m) where
  toFun := A.homologyMulValue n m x
  map_add' := A.homologyMulValue_add_right n m x
  map_smul' := fun r y ↦ A.homologyMulValue_smul_right n m r x y

/-- The right-multiplication linear map is additive in its left input. -/
theorem homologyMulRight_add (A : ChainDGAlgebra.{u, v} R) (n m : ℕ)
    (x y : A.homologyPiece n) :
    A.homologyMulRight n m (x + y) = A.homologyMulRight n m x + A.homologyMulRight n m y :=
  sorry

/-- The right-multiplication linear map is linear in its left input. -/
theorem homologyMulRight_smul (A : ChainDGAlgebra.{u, v} R) (n m : ℕ)
    (r : R) (x : A.homologyPiece n) :
    A.homologyMulRight n m (r • x) = r • A.homologyMulRight n m x := sorry

/-- The homogeneous bilinear multiplication on canonical homology modules. -/
def homologyMul (A : ChainDGAlgebra.{u, v} R) (n m : ℕ) :
    A.homologyPiece n →ₗ[R] A.homologyPiece m →ₗ[R] A.homologyPiece (n + m) where
  toFun := A.homologyMulRight n m
  map_add' := A.homologyMulRight_add n m
  map_smul' := A.homologyMulRight_smul n m

/-- On classes represented by specified cycles, homology multiplication is represented by the
chain-level product. -/
theorem homologyMul_class (A : ChainDGAlgebra.{u, v} R) (n m : ℕ)
    (x : A.cycles (n : ℤ)) (y : A.cycles (m : ℤ)) :
    A.homologyMul n m (A.homologyπ n x) (A.homologyπ m y) =
      A.homologyπ (n + m) (A.cyclesMul n m x y) := sorry

/-- The chain-level unit is a degree-zero cycle. -/
theorem d_one_eq_zero (A : ChainDGAlgebra.{u, v} R) :
    ((forget₂ (ModuleCat.{v} R) Ab).map (A.toChainComplex.d 0 (-1))) A.one = 0 := sorry

/-- The chain-complex successor of degree zero is degree minus one. -/
theorem down_next_zero : (ComplexShape.down ℤ).next 0 = -1 := sorry

/-- The unit cycle of a chain DGA. -/
def oneCycle (A : ChainDGAlgebra.{u, v} R) : A.cycles 0 :=
  A.toChainComplex.cyclesMk A.one (-1) down_next_zero A.d_one_eq_zero

/-- The unit class in degree-zero homology. -/
def homologyOne (A : ChainDGAlgebra.{u, v} R) : A.homologyPiece 0 :=
  A.homologyπ 0 A.oneCycle

/-- The canonical multiplication operation on nonnegative homology pieces. -/
noncomputable instance homologyGMul (A : ChainDGAlgebra.{u, v} R) :
    GradedMonoid.GMul A.homologyPiece where
  mul := fun x y ↦ A.homologyMul _ _ x y

/-- The canonical unit on nonnegative homology pieces. -/
noncomputable instance homologyGOne (A : ChainDGAlgebra.{u, v} R) :
    GradedMonoid.GOne A.homologyPiece where
  one := A.homologyOne

/-- The homology unit acts on the left. -/
theorem homology_one_mul (A : ChainDGAlgebra.{u, v} R) (x : GradedMonoid A.homologyPiece) :
    1 * x = x := sorry

/-- The homology unit acts on the right. -/
theorem homology_mul_one (A : ChainDGAlgebra.{u, v} R) (x : GradedMonoid A.homologyPiece) :
    x * 1 = x := sorry

/-- Homology multiplication is associative. -/
theorem homology_mul_assoc (A : ChainDGAlgebra.{u, v} R) (x y z : GradedMonoid A.homologyPiece) :
    x * y * z = x * (y * z) := sorry

/-- Homology multiplication sends a zero right factor to zero. -/
theorem homologyMul_zero (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (x : A.homologyPiece n) :
    GradedMonoid.GMul.mul x (0 : A.homologyPiece m) = 0 := sorry

/-- Homology multiplication sends a zero left factor to zero. -/
theorem zero_homologyMul (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (y : A.homologyPiece m) :
    GradedMonoid.GMul.mul (0 : A.homologyPiece n) y = 0 := sorry

/-- Homology multiplication distributes over addition on the right. -/
theorem homologyMul_add (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (x : A.homologyPiece n) (y z : A.homologyPiece m) :
    GradedMonoid.GMul.mul x (y + z) =
      GradedMonoid.GMul.mul x y + GradedMonoid.GMul.mul x z := sorry

/-- Homology multiplication distributes over addition on the left. -/
theorem add_homologyMul (A : ChainDGAlgebra.{u, v} R) {n m : ℕ}
    (x y : A.homologyPiece n) (z : A.homologyPiece m) :
    GradedMonoid.GMul.mul (x + y) z =
      GradedMonoid.GMul.mul x z + GradedMonoid.GMul.mul y z := sorry

/-- The nonnegative homology pieces inherit the distributive homogeneous multiplication laws. -/
noncomputable instance homologyGNonUnitalNonAssocSemiring (A : ChainDGAlgebra.{u, v} R) :
    DirectSum.GNonUnitalNonAssocSemiring A.homologyPiece where
  mul_zero := A.homologyMul_zero
  zero_mul := A.zero_homologyMul
  mul_add := A.homologyMul_add
  add_mul := A.add_homologyMul

/-- The nonnegative homology pieces inherit the homogeneous monoid laws. -/
noncomputable instance homologyGMonoid (A : ChainDGAlgebra.{u, v} R) :
    GradedMonoid.GMonoid A.homologyPiece where
  one_mul := A.homology_one_mul
  mul_one := A.homology_mul_one
  mul_assoc := A.homology_mul_assoc

/-- The natural-number cast in degree-zero homology. -/
def homologyNatCast (A : ChainDGAlgebra.{u, v} R) (n : ℕ) : A.homologyPiece 0 :=
  n • A.homologyOne

/-- The degree-zero homology cast sends zero to zero. -/
theorem homologyNatCast_zero (A : ChainDGAlgebra.{u, v} R) : A.homologyNatCast 0 = 0 := sorry

/-- The degree-zero homology cast preserves successors. -/
theorem homologyNatCast_succ (A : ChainDGAlgebra.{u, v} R) (n : ℕ) :
    A.homologyNatCast (n + 1) = A.homologyNatCast n + A.homologyOne := sorry

/-- The nonnegative homology pieces form a graded semiring. -/
noncomputable instance homologyGSemiring (A : ChainDGAlgebra.{u, v} R) :
    DirectSum.GSemiring A.homologyPiece where
  natCast := A.homologyNatCast
  natCast_zero := A.homologyNatCast_zero
  natCast_succ := A.homologyNatCast_succ

/-- The structural scalar map into degree-zero homology. -/
def homologyAlgebraMap (A : ChainDGAlgebra.{u, v} R) : R →+ A.homologyPiece 0 :=
  (LinearMap.toSpanSingleton R (A.homologyPiece 0) A.homologyOne).toAddMonoidHom

/-- The homology scalar map preserves one. -/
theorem homologyAlgebraMap_one (A : ChainDGAlgebra.{u, v} R) :
    A.homologyAlgebraMap 1 = GradedMonoid.GOne.one := sorry

/-- The homology scalar map preserves multiplication. -/
theorem homologyAlgebraMap_mul (A : ChainDGAlgebra.{u, v} R) (r s : R) :
    GradedMonoid.mk 0 (A.homologyAlgebraMap (r * s)) =
      GradedMonoid.mk 0
        (GradedMonoid.GMul.mul (A.homologyAlgebraMap r) (A.homologyAlgebraMap s)) := sorry

/-- Scalars commute with every homogeneous homology class. -/
theorem homologyAlgebraMap_commutes (A : ChainDGAlgebra.{u, v} R) (r : R)
    (x : GradedMonoid A.homologyPiece) :
    GradedMonoid.mk 0 (A.homologyAlgebraMap r) * x =
      x * GradedMonoid.mk 0 (A.homologyAlgebraMap r) := sorry

/-- Scalar multiplication agrees with multiplication by the degree-zero scalar class. -/
theorem homologyAlgebraMap_smul (A : ChainDGAlgebra.{u, v} R) (r : R)
    (x : GradedMonoid A.homologyPiece) :
    r • x = GradedMonoid.mk 0 (A.homologyAlgebraMap r) * x := sorry

/-- The nonnegative homology pieces inherit their graded `R`-algebra structure. -/
noncomputable instance homologyGAlgebra (A : ChainDGAlgebra.{u, v} R) :
    DirectSum.GAlgebra R A.homologyPiece where
  toFun := A.homologyAlgebraMap
  map_one := A.homologyAlgebraMap_one
  map_mul := A.homologyAlgebraMap_mul
  commutes := A.homologyAlgebraMap_commutes
  smul_def := A.homologyAlgebraMap_smul

/-- Graded commutativity descends to homology. -/
theorem homology_mul_comm (A : ChainDGAlgebra.{u, v} R) [A.IsCommutative]
    (n m : ℕ) (x : A.homologyPiece n) (y : A.homologyPiece m) :
    GradedMonoid.GMul.mul x y =
      cast (congrArg A.homologyPiece (Nat.add_comm m n))
        (((-1 : R) ^ (n * m)) • GradedMonoid.GMul.mul y x) := sorry

/-- Odd-degree homology classes have square zero in a strictly commutative chain DGA. -/
theorem homology_sq_eq_zero_of_odd (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative]
    {n : ℕ} (hn : Odd n) (x : A.homologyPiece n) :
    GradedMonoid.GMul.mul x x = 0 := sorry

/-- Strict graded commutativity descends canonically to nonnegative homology. -/
noncomputable instance homologyIsStrictlyCommutative
    (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    DirectSum.Graded.IsStrictlyCommutative R A.homologyPiece where
  mul_comm := A.homology_mul_comm
  sq_eq_zero_of_odd := A.homology_sq_eq_zero_of_odd

/-- The canonical nonnegatively graded algebra carried by the Mathlib homology modules of a
strictly commutative chain DGA. -/
noncomputable def homologyNonnegativePart
    (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    NonnegGradedAlgebra.{u, v} R where
  piece := A.homologyPiece
  pieceAddCommGroup := fun _ ↦ inferInstance
  pieceModule := fun _ ↦ inferInstance
  pieceGSemiring := A.homologyGSemiring
  pieceGAlgebra := A.homologyGAlgebra
  pieceIsStrictlyCommutative := A.homologyIsStrictlyCommutative

namespace Hom

variable {A B C : ChainDGAlgebra.{u, v} R}

/-- The linear map on degree-`n` homology induced by a chain-DGA homomorphism. -/
noncomputable def homologyLinearMap (f : Hom A B) (n : ℤ) :
    A.homology n →ₗ[R] B.homology n :=
  (HomologicalComplex.homologyMap f.toChainMap n).hom

/-- Evaluation of the induced homology linear map is evaluation of Mathlib's canonical homology
map for the underlying chain map. -/
@[simp] theorem homologyLinearMap_apply (f : Hom A B) (n : ℤ) (x : A.homology n) :
    f.homologyLinearMap n x =
      (HomologicalComplex.homologyMap f.toChainMap n).hom x := sorry

/-- The induced homology map sends a cycle class to the class of the mapped cycle. -/
@[simp] theorem homologyLinearMap_homologyπ (f : Hom A B) (n : ℤ) (x : A.cycles n) :
    f.homologyLinearMap n (A.homologyπ n x) =
      B.homologyπ n (HomologicalComplex.cyclesMap f.toChainMap n x) := sorry

/-- The identity chain-DGA homomorphism induces the identity on homology. -/
@[simp] theorem homologyLinearMap_id (A : ChainDGAlgebra.{u, v} R) (n : ℤ) :
    (id A).homologyLinearMap n = LinearMap.id := sorry

/-- The homology linear map of a composite is the composite of the homology linear maps. -/
@[simp] theorem homologyLinearMap_comp (g : Hom B C) (f : Hom A B) (n : ℤ) :
    (comp g f).homologyLinearMap n =
      (g.homologyLinearMap n).comp (f.homologyLinearMap n) := sorry

/-- The induced homology map preserves the degree-zero unit class. -/
@[simp] theorem homologyLinearMap_one (f : Hom A B) :
    f.homologyLinearMap 0 A.homologyOne = B.homologyOne := sorry

/-- The induced homology map preserves homogeneous multiplication. -/
@[simp] theorem homologyLinearMap_mul (f : Hom A B) (n m : ℕ)
    (x : A.homologyPiece n) (y : A.homologyPiece m) :
    f.homologyLinearMap (n + m) (A.homologyMul n m x y) =
      B.homologyMul n m (f.homologyLinearMap n x) (f.homologyLinearMap m y) := sorry

/-- A chain-DGA homomorphism induces a degree-preserving homomorphism between the canonical
nonnegative graded algebras on homology. -/
noncomputable def homologyHom (f : Hom A B)
    [A.IsStrictlyCommutative] [B.IsStrictlyCommutative] :
    NonnegGradedAlgebra.Hom A.homologyNonnegativePart B.homologyNonnegativePart where
  map n := f.homologyLinearMap n
  map_one := f.homologyLinearMap_one
  map_mul := f.homologyLinearMap_mul

/-- The degree-`n` linear map stored by `homologyHom` is the canonical homology linear map. -/
@[simp] theorem homologyHom_map (f : Hom A B)
    [A.IsStrictlyCommutative] [B.IsStrictlyCommutative] (n : ℕ) :
    f.homologyHom.map n = f.homologyLinearMap n := sorry

/-- The homogeneous component of `homologyHom` is the canonical homology linear map. -/
@[simp] theorem homologyHom_apply (f : Hom A B)
    [A.IsStrictlyCommutative] [B.IsStrictlyCommutative]
    (n : ℕ) (x : A.homologyPiece n) :
    f.homologyHom n x = f.homologyLinearMap n x := sorry

/-- The graded homology homomorphism induced by the identity is the identity. -/
@[simp] theorem homologyHom_id (A : ChainDGAlgebra.{u, v} R) [A.IsStrictlyCommutative] :
    (id A).homologyHom = 𝟙 A.homologyNonnegativePart := sorry

/-- The graded homology homomorphism preserves composition. -/
@[simp] theorem homologyHom_comp (g : Hom B C) (f : Hom A B)
    [A.IsStrictlyCommutative] [B.IsStrictlyCommutative] [C.IsStrictlyCommutative] :
    (comp g f).homologyHom =
      NonnegGradedAlgebra.Hom.comp g.homologyHom f.homologyHom := sorry

end Hom

end ChainDGAlgebra
