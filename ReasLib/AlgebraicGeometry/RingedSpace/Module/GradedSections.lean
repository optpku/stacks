module

public import ReasLib.Algebra.Module.GradedNatInt
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections

/-!
# Graded section rings and twisted section modules

For a module sheaf `L`, this file constructs the nonnegative graded section ring of its tensor
powers.  If `L` is invertible, it also constructs the integer-graded section module obtained by
twisting an arbitrary module sheaf by the integral powers of `L`.

The multiplication and action maps are explicit.  Their algebraic laws are separate theorem
statements, so downstream code can reuse the computational data without unfolding structure
instances.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.GradedSections

variable {X : RingedSpace.{u}}

/-- The degree-`n` homogeneous piece of the section ring associated to `L`. -/
@[stacks 01CV "graded ring, homogeneous piece"]
abbrev degree (L : X.Modules) (n : ℕ) : Type _ :=
  (TensorPower.sheaf L n).val.presheaf.obj (op ⊤)

/-- The degree-`n` homogeneous piece of the section module obtained by twisting `F` by an
invertible module sheaf `L`. -/
@[stacks 01CV "twisted graded module, homogeneous piece"]
abbrev twistedDegree
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) (n : ℤ) : Type _ :=
  (F ⊗ (L ^⊗ n)).val.presheaf.obj (op ⊤)

/-- Multiplication of global sections of two tensor powers, before evaluating at the top open. -/
@[stacks 01CV "graded ring, multiplication on compatible sections"]
noncomputable def mulSection
    (L : X.Modules) {m n : ℕ} :
    (TensorPower.sheaf L m).sections → (TensorPower.sheaf L n).sections →
      (TensorPower.sheaf L (m + n)).sections :=
  fun x y ↦ SheafOfModules.sectionsMap (TensorPower.addIso L m n).hom
    (tensorSection (X := X) (ℱ := TensorPower.sheaf L m)
      (𝒢 := TensorPower.sheaf L n) x y)

/-- Homogeneous multiplication of sections of nonnegative tensor powers. -/
@[stacks 01CV "graded ring, homogeneous multiplication"]
noncomputable def mul
    (L : X.Modules) {m n : ℕ} :
    degree L m → degree L n → degree L (m + n) :=
  fun x y ↦ sectionsEquivTop (TensorPower.sheaf L (m + n))
    (mulSection L (sectionFromTop (TensorPower.sheaf L m) x)
      (sectionFromTop (TensorPower.sheaf L n) y))

/-- The degree-zero unit in the graded section ring. -/
@[stacks 01CV "graded ring, homogeneous unit"]
noncomputable def one (L : X.Modules) : degree L 0 :=
  (eqToHom (TensorPower.zero L).symm).val.app (op ⊤) (unitTopValue X)

/-- A global function, viewed as a degree-zero section of the tensor-power section ring. -/
@[stacks 01CV "global functions in degree zero"]
noncomputable def scalar (L : X.Modules) (r : globalSectionsRing X) : degree L 0 :=
  r • one L

/-- The degree-zero scalar map sends zero to zero. -/
theorem scalar_zero (L : X.Modules) :
    scalar L 0 = 0 := sorry

/-- The degree-zero scalar map preserves addition. -/
theorem scalar_add (L : X.Modules) (r s : globalSectionsRing X) :
    scalar L (r + s) = scalar L r + scalar L s := sorry

/-- Global functions map additively to the degree-zero piece of the section ring. -/
@[stacks 01CV "global functions in the degree-zero piece"]
noncomputable def scalarHom (L : X.Modules) :
    globalSectionsRing X →+ degree L 0 where
  toFun := scalar L
  map_zero' := scalar_zero L
  map_add' := scalar_add L

/-- The additive degree-zero scalar map has the expected underlying function. -/
@[simp]
theorem scalarHom_apply (L : X.Modules) (r : globalSectionsRing X) :
    scalarHom L r = scalar L r := sorry

/-- The unit global function maps to the graded unit. -/
theorem scalar_one (L : X.Modules) :
    scalar L 1 = one L := sorry

/-- The canonical comparison used by the twisted graded action. -/
@[stacks 01CV "twisted graded module, action comparison"]
noncomputable def actionIso
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) (m : ℕ) (n : ℤ) :
    TensorPower.sheaf L m ⊗ (F ⊗ (L ^⊗ n)) ≅
      F ⊗ (L ^⊗ ((m : ℤ) + n)) :=
  (InvertiblePower.natIso L m ⊗ᵢ Iso.refl (F ⊗ (L ^⊗ n))) ≪≫
    (α_ (L ^⊗ (m : ℤ)) F (L ^⊗ n)).symm ≪≫
    ((β_ (L ^⊗ (m : ℤ)) F) ⊗ᵢ Iso.refl (L ^⊗ n)) ≪≫
    α_ F (L ^⊗ (m : ℤ)) (L ^⊗ n) ≪≫
    (Iso.refl F ⊗ᵢ InvertiblePower.addIso L (m : ℤ) n)

/-- Action of a tensor-power section on a twisted global section, before evaluating at the top
open. -/
@[stacks 01CV "twisted graded module, action on compatible sections"]
noncomputable def smulSection
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) {m : ℕ} {n : ℤ} :
    (TensorPower.sheaf L m).sections → (F ⊗ (L ^⊗ n)).sections →
      (F ⊗ (L ^⊗ ((m : ℤ) + n))).sections :=
  fun x y ↦ SheafOfModules.sectionsMap (actionIso L F m n).hom
    (tensorSection (X := X) (ℱ := TensorPower.sheaf L m)
      (𝒢 := F ⊗ (L ^⊗ n)) x y)

/-- Homogeneous action of the section ring on the twisted section pieces. -/
@[stacks 01CV "twisted graded module, homogeneous action"]
noncomputable def smul
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) {m : ℕ} {n : ℤ} :
    degree L m → twistedDegree L F n → twistedDegree L F ((m : ℤ) + n) :=
  fun x y ↦ sectionsEquivTop (F ⊗ (L ^⊗ ((m : ℤ) + n)))
    (smulSection L F (sectionFromTop (TensorPower.sheaf L m) x)
      (sectionFromTop (F ⊗ (L ^⊗ n)) y))

/-- The nonnegative graded section ring associated to `L`. -/
@[stacks 01CV "graded ring"]
abbrev ring (L : X.Modules) : Type _ :=
  ⨁ n : ℕ, degree L n

/-- The integer-graded section module obtained by twisting `F` by the integral powers of an
invertible module sheaf `L`. -/
@[stacks 01CV "twisted graded module"]
abbrev twisted
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) : Type _ :=
  ⨁ n : ℤ, twistedDegree L F n

/-- Right multiplication by zero vanishes on homogeneous section-ring pieces. -/
theorem mul_zero
    (L : X.Modules) {m n : ℕ} (x : degree L m) :
    mul L x (0 : degree L n) = 0 := sorry

/-- Left multiplication by zero vanishes on homogeneous section-ring pieces. -/
theorem zero_mul
    (L : X.Modules) {m n : ℕ} (y : degree L n) :
    mul L (0 : degree L m) y = 0 := sorry

/-- Homogeneous multiplication distributes over addition in the right variable. -/
theorem mul_add
    (L : X.Modules) {m n : ℕ}
    (x : degree L m) (y z : degree L n) :
    mul L x (y + z) = mul L x y + mul L x z := sorry

/-- Homogeneous multiplication distributes over addition in the left variable. -/
theorem add_mul
    (L : X.Modules) {m n : ℕ}
    (x y : degree L m) (z : degree L n) :
    mul L (x + y) z = mul L x z + mul L y z := sorry

/-- The explicit homogeneous multiplication supplies the additive graded multiplication data. -/
noncomputable instance instGNonUnitalNonAssocSemiring (L : X.Modules) :
    DirectSum.GNonUnitalNonAssocSemiring (degree L) where
  mul := fun x y ↦ mul L x y
  mul_zero := mul_zero L
  zero_mul := zero_mul L
  mul_add := mul_add L
  add_mul := add_mul L

/-- The explicit degree-zero section supplies the graded unit data. -/
noncomputable instance instGOne (L : X.Modules) :
    GradedMonoid.GOne (degree L) where
  one := one L

/-- The graded unit is a left identity. -/
theorem one_mul (L : X.Modules) (x : GradedMonoid (degree L)) :
    (1 : GradedMonoid (degree L)) * x = x := sorry

/-- The graded unit is a right identity. -/
theorem mul_one (L : X.Modules) (x : GradedMonoid (degree L)) :
    x * (1 : GradedMonoid (degree L)) = x := sorry

/-- Homogeneous multiplication is associative. -/
theorem mul_assoc
    (L : X.Modules) (x y z : GradedMonoid (degree L)) :
    x * y * z = x * (y * z) := sorry

/-- The homogeneous section-ring pieces form a graded monoid. -/
noncomputable instance instGMonoid (L : X.Modules) :
    GradedMonoid.GMonoid (degree L) where
  one_mul := one_mul L
  mul_one := mul_one L
  mul_assoc := mul_assoc L

/-- The natural-number cast in degree zero. -/
noncomputable def natCast (L : X.Modules) (n : ℕ) : degree L 0 :=
  n • one L

/-- The degree-zero natural-number cast sends zero to zero. -/
theorem natCast_zero (L : X.Modules) :
    natCast L 0 = 0 := sorry

/-- The degree-zero natural-number cast respects successors. -/
theorem natCast_succ (L : X.Modules) (n : ℕ) :
    natCast L (n + 1) = natCast L n + one L := sorry

/-- The homogeneous section-ring pieces form a graded semiring. -/
noncomputable instance instGSemiring (L : X.Modules) :
    DirectSum.GSemiring (degree L) where
  natCast := natCast L
  natCast_zero := natCast_zero L
  natCast_succ := natCast_succ L

/-- The integer cast in degree zero. -/
noncomputable def intCast (L : X.Modules) (z : ℤ) : degree L 0 :=
  z • one L

/-- The degree-zero integer cast extends the natural-number cast. -/
theorem intCast_ofNat (L : X.Modules) (n : ℕ) :
    intCast L n = natCast L n := sorry

/-- The degree-zero integer cast has the canonical negative-successor value. -/
theorem intCast_negSucc (L : X.Modules) (n : ℕ) :
    intCast L (Int.negSucc n) = -natCast L (n + 1) := sorry

/-- The homogeneous section-ring pieces form a graded ring. -/
noncomputable instance instGRing (L : X.Modules) :
    DirectSum.GRing (degree L) where
  intCast := intCast L
  intCast_ofNat := intCast_ofNat L
  intCast_negSucc_ofNat := intCast_negSucc L

/-- Multiplication of global functions is multiplication in degree zero. -/
theorem scalar_mul (L : X.Modules) (r s : globalSectionsRing X) :
    GradedMonoid.mk 0 (scalar L (r * s)) =
      GradedMonoid.mk (0 + 0) (mul L (scalar L r) (scalar L s)) := sorry

/-- Degree-zero global functions commute with every homogeneous section. -/
theorem scalar_commutes
    (L : X.Modules) (r : globalSectionsRing X) (x : GradedMonoid (degree L)) :
    GradedMonoid.mk 0 (scalar L r) * x =
      x * GradedMonoid.mk 0 (scalar L r) := sorry

/-- The sectionwise action of a global function is multiplication by its degree-zero image. -/
theorem scalar_smul
    (L : X.Modules) (r : globalSectionsRing X) (x : GradedMonoid (degree L)) :
    r • x = GradedMonoid.mk 0 (scalar L r) * x := sorry

/-- The tensor-power section ring is canonically an algebra over the global functions on `X`. -/
@[stacks 01CV "graded section algebra over global functions"]
noncomputable instance instGAlgebra (L : X.Modules) :
    DirectSum.GAlgebra (globalSectionsRing X) (degree L) where
  toFun := scalarHom L
  map_one := scalar_one L
  map_mul := scalar_mul L
  commutes := scalar_commutes L
  smul_def := scalar_smul L

/-- The algebra map from global functions is inclusion through the degree-zero scalar map. -/
@[stacks 01CV "global-functions map to the graded section algebra", simp]
theorem algebraMap_apply (L : X.Modules) (r : globalSectionsRing X) :
    algebraMap (globalSectionsRing X) (ring L) r =
      DirectSum.of (degree L) 0 (scalar L r) := sorry

/-- For an invertible module sheaf, homogeneous multiplication is graded-commutative. -/
@[stacks 01CV "graded commutativity for an invertible module"]
theorem mul_comm
    (L : X.Modules) [isInvertibleObject L]
    (x y : GradedMonoid (degree L)) :
    x * y = y * x := sorry

/-- The homogeneous powers of an invertible module sheaf form a graded commutative monoid. -/
@[stacks 01CV "graded commutative monoid structure"]
noncomputable instance instGCommMonoid
    (L : X.Modules) [isInvertibleObject L] :
    GradedMonoid.GCommMonoid (degree L) where
  mul_comm := mul_comm L

/-- The homogeneous powers of an invertible module sheaf form a graded commutative semiring. -/
@[stacks 01CV "graded commutative semiring structure"]
noncomputable instance instGCommSemiring
    (L : X.Modules) [isInvertibleObject L] :
    DirectSum.GCommSemiring (degree L) where

/-- The canonical graded commutative-ring structure on the section ring. -/
@[stacks 01CV "graded ring, commutative-ring structure"]
noncomputable instance instGCommRing
    (L : X.Modules) [isInvertibleObject L] :
    DirectSum.GCommRing (degree L) where

/-- The explicit homogeneous action supplies graded scalar multiplication. -/
noncomputable instance instGSMul
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) :
    GradedMonoid.GSMul (degree L) (twistedDegree L F) where
  smul := fun x y ↦ smul L F x y

/-- The graded unit acts trivially on every twisted homogeneous element. -/
theorem one_smul
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) (x : GradedMonoid (twistedDegree L F)) :
    (1 : GradedMonoid (degree L)) • x = x := sorry

/-- Homogeneous multiplication and the twisted homogeneous action are associative. -/
theorem mul_smul
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) (a b : GradedMonoid (degree L))
    (x : GradedMonoid (twistedDegree L F)) :
    (a * b) • x = a • b • x := sorry

/-- The twisted homogeneous pieces carry the canonical graded multiplicative action. -/
noncomputable instance instGMulAction
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) :
    GradedMonoid.GMulAction (degree L) (twistedDegree L F) where
  one_smul := one_smul L F
  mul_smul := mul_smul L F

/-- The homogeneous action distributes over addition in the module variable. -/
theorem smul_add
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) {m : ℕ} {n : ℤ}
    (a : degree L m) (x y : twistedDegree L F n) :
    smul L F a (x + y) = smul L F a x + smul L F a y := sorry

/-- Every homogeneous section acts trivially on zero. -/
theorem smul_zero
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) {m : ℕ} {n : ℤ} (a : degree L m) :
    smul L F a (0 : twistedDegree L F n) = 0 := sorry

/-- The twisted homogeneous action is additive in the module variable. -/
noncomputable instance instGdistribMulAction
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) :
    DirectSum.GdistribMulAction (degree L) (twistedDegree L F) where
  smul_add := smul_add L F
  smul_zero := smul_zero L F

/-- The homogeneous action distributes over addition in the scalar variable. -/
theorem add_smul
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) {m : ℕ} {n : ℤ}
    (a b : degree L m) (x : twistedDegree L F n) :
    smul L F (a + b) x = smul L F a x + smul L F b x := sorry

/-- The zero homogeneous scalar acts trivially. -/
theorem zero_smul
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) {m : ℕ} {n : ℤ} (x : twistedDegree L F n) :
    smul L F (0 : degree L m) x = 0 := sorry

/-- The canonical graded-module structure on the twisted section pieces. -/
@[stacks 01CV "twisted graded module, module structure"]
noncomputable instance instGmodule
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) :
    DirectSum.Gmodule (degree L) (twistedDegree L F) where
  add_smul := add_smul L F
  zero_smul := zero_smul L F

/-- The global-function action and the graded section-ring action on twisted sections form the
canonical scalar tower. -/
@[stacks 01CV "global functions acting through the graded section algebra"]
instance instIsScalarTowerTwisted (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) :
    IsScalarTower (globalSectionsRing X) (ring L) (twisted L F) := sorry

/-- Global functions commute with the graded section-ring action on twisted sections. -/
@[stacks 01CV "commuting global and graded scalar actions"]
instance instSMulCommClassTwisted (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) :
    SMulCommClass (globalSectionsRing X) (ring L) (twisted L F) := sorry

/-- Pure homogeneous summands multiply through the explicit twisted action. -/
@[simp]
theorem of_smul_of
    (L : X.Modules) [isInvertibleObject L]
    (F : X.Modules) {m : ℕ} {n : ℤ}
    (x : degree L m) (y : twistedDegree L F n) :
    DirectSum.of (degree L) m x • DirectSum.of (twistedDegree L F) n y =
      DirectSum.of (twistedDegree L F) ((m : ℤ) + n) (smul L F x y) := sorry

end AlgebraicGeometry.RingedSpace.GradedSections

