module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Left

/-!
# Products of Differential Graded Modules

Products of left and right modules over a fixed cochain differential graded algebra are
computed degreewise.  This leaf exposes the concrete products, their coordinate maps, and their
universal properties before registering the corresponding categorical products.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory CategoryTheory.Limits

namespace LeftDifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R}

namespace Product

variable {ι : Type v}
variable (M : ι → LeftDifferentialGradedModule.{u, max v w} A)

/-- The componentwise differential on the degreewise product of left differential graded
modules. -/
def d (n : ℤ) :
    (∀ j : ι, (M j).X n) →ₗ[R] (∀ j : ι, (M j).X (n + 1)) :=
  LinearMap.piMap fun j ↦ (M j).d n

/-- The product differential is evaluated coordinatewise. -/
@[simp] theorem d_apply (n : ℤ) (x : ∀ j : ι, (M j).X n) (j : ι) :
    d M n x j = (M j).d n (x j) := sorry

/-- The componentwise action of a fixed homogeneous algebra element on a degreewise product. -/
def smulValue (i p : ℤ) (a : A.X i) :
    (∀ j : ι, (M j).X p) →ₗ[R] (∀ j : ι, (M j).X (i + p)) :=
  LinearMap.piMap fun j ↦ (M j).smul i p a

/-- The fixed-element product action is evaluated coordinatewise. -/
@[simp] theorem smulValue_apply (i p : ℤ) (a : A.X i)
    (x : ∀ j : ι, (M j).X p) (j : ι) :
    smulValue M i p a x j = (M j).smul i p a (x j) := sorry

/-- The fixed-element product action is additive in the algebra element. -/
theorem smulValue_add (i p : ℤ) (a b : A.X i) :
    smulValue M i p (a + b) = smulValue M i p a + smulValue M i p b := sorry

/-- The fixed-element product action respects scalar multiplication in the algebra element. -/
theorem smulValue_smul (i p : ℤ) (r : R) (a : A.X i) :
    smulValue M i p (r • a) = r • smulValue M i p a := sorry

/-- The componentwise homogeneous left action on a degreewise product. -/
def smul (i p : ℤ) :
    A.X i →ₗ[R] (∀ j : ι, (M j).X p) →ₗ[R] (∀ j : ι, (M j).X (i + p)) where
  toFun a := smulValue M i p a
  map_add' := smulValue_add M i p
  map_smul' := smulValue_smul M i p

/-- The product action is evaluated coordinatewise. -/
@[simp] theorem smul_apply (i p : ℤ) (a : A.X i)
    (x : ∀ j : ι, (M j).X p) (j : ι) :
    smul M i p a x j = (M j).smul i p a (x j) := sorry

/-- Lemma 22.4.2 (09JJ), left-module form: the explicit degreewise product of a family of left
differential graded modules. -/
@[stacks 09JJ "degreewise products of left differential graded modules"]
def obj : LeftDifferentialGradedModule.{u, max v w} A where
  X n := ModuleCat.of.{max v w} R (∀ j : ι, (M j).X n)
  d n := d M n
  smul i p := smul M i p
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The degree-`n` term of the explicit product is the product of the degree-`n` terms. -/
@[simp] theorem obj_X (n : ℤ) :
    (obj M).X n = ModuleCat.of.{max v w} R (∀ j : ι, (M j).X n) := sorry

/-- The differential of the explicit product is componentwise. -/
@[simp] theorem obj_d (n : ℤ) : (obj M).d n = d M n := sorry

/-- The left action on the explicit product is componentwise. -/
@[simp] theorem obj_smul (i p : ℤ) : (obj M).smul i p = smul M i p := sorry

/-- The projection from the explicit product to one coordinate. -/
def proj (j : ι) : obj M ⟶ M j where
  hom n := LinearMap.proj j
  comm_d := sorry
  comm_smul := sorry

/-- A product projection is the coordinate projection in every degree. -/
@[simp] theorem proj_hom (j : ι) (n : ℤ) :
    (proj M j).hom n =
      (LinearMap.proj j : (∀ k : ι, (M k).X n) →ₗ[R] (M j).X n) := sorry

/-- A product projection evaluates a homogeneous element at its coordinate. -/
@[simp] theorem proj_apply (j : ι) (n : ℤ) (x : (obj M).X n) :
    (proj M j).hom n x = x j := sorry

/-- The coordinatewise map into the explicit product. -/
def lift {P : LeftDifferentialGradedModule.{u, max v w} A}
    (f : ∀ j : ι, P ⟶ M j) : P ⟶ obj M where
  hom n := LinearMap.pi fun j ↦ (f j).hom n
  comm_d := sorry
  comm_smul := sorry

/-- The homogeneous component of a map into the explicit product is the linear-map product of
its coordinates. -/
@[simp] theorem lift_hom {P : LeftDifferentialGradedModule.{u, max v w} A}
    (f : ∀ j : ι, P ⟶ M j) (n : ℤ) :
    (lift M f).hom n = LinearMap.pi fun j ↦ (f j).hom n := sorry

/-- A map into the explicit product is evaluated coordinatewise. -/
@[simp] theorem lift_apply {P : LeftDifferentialGradedModule.{u, max v w} A}
    (f : ∀ j : ι, P ⟶ M j) (n : ℤ) (x : P.X n) (j : ι) :
    (lift M f).hom n x j = (f j).hom n x := sorry

/-- The explicit product and its coordinate projections form a fan. -/
def fan : Fan M := Fan.mk (obj M) (proj M)

/-- The point of the explicit product fan is the degreewise product. -/
@[simp] theorem fan_pt : (fan M).pt = obj M := sorry

/-- The legs of the explicit product fan are the coordinate projections. -/
@[simp] theorem fan_proj (j : ι) : (fan M).proj j = proj M j := sorry

/-- Lifting a family of maps and then projecting recovers that family. -/
@[reassoc (attr := simp)] theorem lift_proj
    {P : LeftDifferentialGradedModule.{u, max v w} A}
    (f : ∀ j : ι, P ⟶ M j) (j : ι) :
    lift M f ≫ proj M j = f j := sorry

/-- Maps into the explicit product are determined by their coordinate projections. -/
@[ext] theorem hom_ext {P : LeftDifferentialGradedModule.{u, max v w} A}
    (f g : P ⟶ obj M) (h : ∀ j : ι, f ≫ proj M j = g ≫ proj M j) : f = g := sorry

/-- The chosen lift from any fan has the required projection equations. -/
theorem lift_fan_proj (s : Fan M) (j : ι) :
    lift M s.proj ≫ (fan M).proj j = s.proj j := sorry

/-- The chosen lift from a fan is the unique map satisfying the projection equations. -/
theorem lift_fan_unique (s : Fan M) (f : s.pt ⟶ (fan M).pt)
    (h : ∀ j : ι, f ≫ (fan M).proj j = s.proj j) :
    f = lift M s.proj := sorry

/-- The explicit degreewise product fan is limiting. -/
def isLimit : IsLimit (fan M) :=
  Fan.IsLimit.mk (fan M) (fun s ↦ lift M s.proj)
    (lift_fan_proj M) (lift_fan_unique M)

end Product

/-- Lemma 22.4.2 (09JJ), left-module form: left differential graded modules over a fixed algebra
have arbitrary degreewise products. -/
@[stacks 09JJ "arbitrary products of left differential graded modules"]
instance instHasProducts (A : CochainDGAlgebra.{u, x} R) :
    HasProducts.{v} (LeftDifferentialGradedModule.{u, max v w} A) :=
  hasProducts_of_limit_fans
    (fun M ↦ Product.fan M)
    (fun M ↦ Product.isLimit M)

namespace Product

variable {ι : Type v}
variable (M : ι → LeftDifferentialGradedModule.{u, max v w} A)

/-- The categorical product is canonically isomorphic to the explicit degreewise product. -/
noncomputable def iso : ∏ᶜ M ≅ obj M :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (isLimit M)

/-- The inverse of the concrete-product comparison followed by a categorical projection is the
corresponding explicit projection. -/
@[reassoc (attr := simp)] theorem iso_inv_π (j : ι) :
    (iso M).inv ≫ Pi.π M j = proj M j := sorry

/-- The concrete-product comparison followed by an explicit projection is the corresponding
categorical projection. -/
@[reassoc (attr := simp)] theorem iso_hom_proj (j : ι) :
    (iso M).hom ≫ proj M j = Pi.π M j := sorry

end Product

end LeftDifferentialGradedModule

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R}

namespace Product

variable {ι : Type v}
variable (M : ι → DifferentialGradedModule.{u, max v w} A)

/-- The componentwise differential on the degreewise product of right differential graded
modules. -/
def d (n : ℤ) :
    (∀ j : ι, (M j).X n) →ₗ[R] (∀ j : ι, (M j).X (n + 1)) :=
  LinearMap.piMap fun j ↦ (M j).d n

/-- The product differential is evaluated coordinatewise. -/
@[simp] theorem d_apply (n : ℤ) (x : ∀ j : ι, (M j).X n) (j : ι) :
    d M n x j = (M j).d n (x j) := sorry

/-- The componentwise right action of a fixed homogeneous element of the degreewise product. -/
def smulValue (p i : ℤ) (x : ∀ j : ι, (M j).X p) :
    A.X i →ₗ[R] (∀ j : ι, (M j).X (p + i)) :=
  LinearMap.pi fun j ↦ (M j).smul p i (x j)

/-- The fixed-element product action is evaluated coordinatewise. -/
@[simp] theorem smulValue_apply (p i : ℤ) (x : ∀ j : ι, (M j).X p)
    (a : A.X i) (j : ι) :
    smulValue M p i x a j = (M j).smul p i (x j) a := sorry

/-- The fixed-element product action is additive in the module element. -/
theorem smulValue_add (p i : ℤ) (x y : ∀ j : ι, (M j).X p) :
    smulValue M p i (x + y) = smulValue M p i x + smulValue M p i y := sorry

/-- The fixed-element product action respects scalar multiplication in the module element. -/
theorem smulValue_smul (p i : ℤ) (r : R) (x : ∀ j : ι, (M j).X p) :
    smulValue M p i (r • x) = r • smulValue M p i x := sorry

/-- The componentwise homogeneous right action on a degreewise product. -/
def smul (p i : ℤ) :
    (∀ j : ι, (M j).X p) →ₗ[R] A.X i →ₗ[R] (∀ j : ι, (M j).X (p + i)) where
  toFun x := smulValue M p i x
  map_add' := smulValue_add M p i
  map_smul' := smulValue_smul M p i

/-- The product action is evaluated coordinatewise. -/
@[simp] theorem smul_apply (p i : ℤ) (x : ∀ j : ι, (M j).X p)
    (a : A.X i) (j : ι) :
    smul M p i x a j = (M j).smul p i (x j) a := sorry

/-- Lemma 22.4.2 (09JJ): the explicit degreewise product of a family of right differential
graded modules. -/
@[stacks 09JJ "degreewise products of right differential graded modules"]
def obj : DifferentialGradedModule.{u, max v w} A where
  X n := ModuleCat.of.{max v w} R (∀ j : ι, (M j).X n)
  d n := d M n
  smul p i := smul M p i
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The degree-`n` term of the explicit product is the product of the degree-`n` terms. -/
@[simp] theorem obj_X (n : ℤ) :
    (obj M).X n = ModuleCat.of.{max v w} R (∀ j : ι, (M j).X n) := sorry

/-- The differential of the explicit product is componentwise. -/
@[simp] theorem obj_d (n : ℤ) : (obj M).d n = d M n := sorry

/-- The right action on the explicit product is componentwise. -/
@[simp] theorem obj_smul (p i : ℤ) : (obj M).smul p i = smul M p i := sorry

/-- The projection from the explicit product to one coordinate. -/
def proj (j : ι) : obj M ⟶ M j where
  hom n := LinearMap.proj j
  comm_d := sorry
  comm_smul := sorry

/-- A product projection is the coordinate projection in every degree. -/
@[simp] theorem proj_hom (j : ι) (n : ℤ) :
    (proj M j).hom n =
      (LinearMap.proj j : (∀ k : ι, (M k).X n) →ₗ[R] (M j).X n) := sorry

/-- A product projection evaluates a homogeneous element at its coordinate. -/
@[simp] theorem proj_apply (j : ι) (n : ℤ) (x : (obj M).X n) :
    (proj M j).hom n x = x j := sorry

/-- The coordinatewise map into the explicit product. -/
def lift {P : DifferentialGradedModule.{u, max v w} A}
    (f : ∀ j : ι, P ⟶ M j) : P ⟶ obj M where
  hom n := LinearMap.pi fun j ↦ (f j).hom n
  comm_d := sorry
  comm_smul := sorry

/-- The homogeneous component of a map into the explicit product is the linear-map product of
its coordinates. -/
@[simp] theorem lift_hom {P : DifferentialGradedModule.{u, max v w} A}
    (f : ∀ j : ι, P ⟶ M j) (n : ℤ) :
    (lift M f).hom n = LinearMap.pi fun j ↦ (f j).hom n := sorry

/-- A map into the explicit product is evaluated coordinatewise. -/
@[simp] theorem lift_apply {P : DifferentialGradedModule.{u, max v w} A}
    (f : ∀ j : ι, P ⟶ M j) (n : ℤ) (x : P.X n) (j : ι) :
    (lift M f).hom n x j = (f j).hom n x := sorry

/-- The explicit product and its coordinate projections form a fan. -/
def fan : Fan M := Fan.mk (obj M) (proj M)

/-- The point of the explicit product fan is the degreewise product. -/
@[simp] theorem fan_pt : (fan M).pt = obj M := sorry

/-- The legs of the explicit product fan are the coordinate projections. -/
@[simp] theorem fan_proj (j : ι) : (fan M).proj j = proj M j := sorry

/-- Lifting a family of maps and then projecting recovers that family. -/
@[reassoc (attr := simp)] theorem lift_proj
    {P : DifferentialGradedModule.{u, max v w} A}
    (f : ∀ j : ι, P ⟶ M j) (j : ι) :
    lift M f ≫ proj M j = f j := sorry

/-- Maps into the explicit product are determined by their coordinate projections. -/
@[ext] theorem hom_ext {P : DifferentialGradedModule.{u, max v w} A}
    (f g : P ⟶ obj M) (h : ∀ j : ι, f ≫ proj M j = g ≫ proj M j) : f = g := sorry

/-- The chosen lift from any fan has the required projection equations. -/
theorem lift_fan_proj (s : Fan M) (j : ι) :
    lift M s.proj ≫ (fan M).proj j = s.proj j := sorry

/-- The chosen lift from a fan is the unique map satisfying the projection equations. -/
theorem lift_fan_unique (s : Fan M) (f : s.pt ⟶ (fan M).pt)
    (h : ∀ j : ι, f ≫ (fan M).proj j = s.proj j) :
    f = lift M s.proj := sorry

/-- The explicit degreewise product fan is limiting. -/
def isLimit : IsLimit (fan M) :=
  Fan.IsLimit.mk (fan M) (fun s ↦ lift M s.proj)
    (lift_fan_proj M) (lift_fan_unique M)

end Product

/-- Lemma 22.4.2 (09JJ): right differential graded modules over a fixed algebra have arbitrary
degreewise products. -/
@[stacks 09JJ "arbitrary products of right differential graded modules"]
instance instHasProducts (A : CochainDGAlgebra.{u, x} R) :
    HasProducts.{v} (DifferentialGradedModule.{u, max v w} A) :=
  hasProducts_of_limit_fans
    (fun M ↦ Product.fan M)
    (fun M ↦ Product.isLimit M)

namespace Product

variable {ι : Type v}
variable (M : ι → DifferentialGradedModule.{u, max v w} A)

/-- The categorical product is canonically isomorphic to the explicit degreewise product. -/
noncomputable def iso : ∏ᶜ M ≅ obj M :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (isLimit M)

/-- The inverse of the concrete-product comparison followed by a categorical projection is the
corresponding explicit projection. -/
@[reassoc (attr := simp)] theorem iso_inv_π (j : ι) :
    (iso M).inv ≫ Pi.π M j = proj M j := sorry

/-- The concrete-product comparison followed by an explicit projection is the corresponding
categorical projection. -/
@[reassoc (attr := simp)] theorem iso_hom_proj (j : ι) :
    (iso M).hom ≫ proj M j = Pi.π M j := sorry

end Product

end DifferentialGradedModule
