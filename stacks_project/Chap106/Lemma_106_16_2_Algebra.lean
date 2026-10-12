/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_9_1_Affine
public import stacks_project.Chap103.Proposition_103_11_1
public import stacks_project.Chap103.Remark_103_11_3_CupProduct
public import stacks_project.Chap106.Lemma_106_16_2_Associated
public import stacks_project.Chap106.Lemma_106_16_5_Kunneth

/-!
# Affine evaluation of a tensor functor

The commutative `B`-algebra `C = F(g_{QCoh,*} O_U)` attached to a right exact
tensor functor `F : QCoh X ⥤ ModuleCat B` and a morphism from an affine
scheme, together with the structure map from `Γ(U.left, ⊤)` and the functor
`M ↦ M ⊗[A] C` on `ModuleCat B`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable {B : Type u} [CommRing B]

/-- The module `C = F(g_{QCoh,*} O_U)`. -/
def algebraModule (F : QCoh X ⥤ ModuleCat.{u} B) {U : Over S} [IsAffine U.left]
    (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    ModuleCat.{u} B :=
  F.obj ((directImage g).obj (structureSheaf (GroupoidsOver.slice U)))

/-- The carrier of `C = F(g_{QCoh,*} O_U)`. -/
def algebraCarrier (F : QCoh X ⥤ ModuleCat.{u} B) {U : Over S} [IsAffine U.left]
    (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] : Type u :=
  algebraModule F g

/-- `algebraCarrier` is the underlying type of `algebraModule`. -/
theorem algebraCarrier_eq (F : QCoh X ⥤ ModuleCat.{u} B) {U : Over S} [IsAffine U.left]
    (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    algebraCarrier F g = algebraModule F g :=
  rfl

/-- Multiplication of `g_{QCoh,*} O_U`, from the naive cup product and
`structureSheafMul`. -/
def directImageStructureSheafMul {U : Over S}
    (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    tensor
        ((directImage g).obj (structureSheaf (GroupoidsOver.slice U)))
        ((directImage g).obj (structureSheaf (GroupoidsOver.slice U))) ⟶
      (directImage g).obj (structureSheaf (GroupoidsOver.slice U)) :=
  directImage_tensorComparison g
      (toLQCohFbc_isRightAdjoint_toQCoh X).some
      (structureSheaf (GroupoidsOver.slice U))
      (structureSheaf (GroupoidsOver.slice U)) ≫
    (directImage g).map (structureSheafMul (GroupoidsOver.slice U))

/-- The `B`-linear multiplication `C ⊗[B] C → C` obtained from `h_tensor` and
`F` of `directImageStructureSheafMul`. -/
def algebraMulLinear (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅ ModuleCat.of B (F.obj M ⊗[B] F.obj N))
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    algebraModule F g ⊗[B] algebraModule F g →ₗ[B] algebraModule F g :=
  ((h_tensor
          ((directImage g).obj (structureSheaf (GroupoidsOver.slice U)))
          ((directImage g).obj (structureSheaf (GroupoidsOver.slice U)))).inv ≫
      F.map (directImageStructureSheafMul g)).hom

/-- The unit `O_X ⟶ g_{QCoh,*} O_U` of the pushforward algebra. -/
def structureSheafDirectImageUnit {U : Over S}
    (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    structureSheaf X ⟶
      (directImage g).obj (structureSheaf (GroupoidsOver.slice U)) :=
  (pullback_directImage_adjunction g).some.unit.app (structureSheaf X) ≫
    (directImage g).map (structureSheafPullbackInv g)

/-- The unit of `C`, obtained from `h_unit` and `structureSheafDirectImageUnit`. -/
def algebraOne (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    algebraCarrier F g :=
  (h_unit.inv ≫ F.map (structureSheafDirectImageUnit g)).hom (1 : B)

/-- `C = F(g_{QCoh,*} O_U)` is a commutative ring. -/
@[reducible] def algebraCommRing (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅ ModuleCat.of B (F.obj M ⊗[B] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    CommRing (algebraCarrier F g) :=
  letI : AddCommGroup (algebraCarrier F g) :=
    inferInstanceAs (AddCommGroup (algebraModule F g : Type u))
  letI : Module B (algebraCarrier F g) :=
    inferInstanceAs (Module B (algebraModule F g : Type u))
  letI : One (algebraCarrier F g) := ⟨algebraOne F h_unit g⟩
  letI : Mul (algebraCarrier F g) :=
    ⟨fun x y ↦ algebraMulLinear F h_tensor g (x ⊗ₜ y)⟩
  { mul := (· * ·)
    one := 1
    mul_assoc := sorry
    one_mul := sorry
    mul_one := sorry
    zero_mul := sorry
    mul_zero := sorry
    left_distrib := sorry
    right_distrib := sorry
    mul_comm := sorry
    npow := npowRec
    npow_zero := sorry
    npow_succ := sorry }

/-- `C` is a `B`-algebra via the `B`-module structure of `F(g_{QCoh,*} O_U)`. -/
@[reducible] def algebraOfB (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅ ModuleCat.of B (F.obj M ⊗[B] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    -- Local instance justification (proof-local temporary data): `Algebra.ofModule`
    -- requires the commutative ring structure induced by `h_tensor` and `h_unit`.
    letI := algebraCommRing F h_tensor h_unit g
    -- Local instance justification (proof-local temporary data): `Algebra.ofModule`
    -- requires the commutative ring structure induced by `h_tensor` and `h_unit`.
    letI : Module B (algebraCarrier F g) :=
      inferInstanceAs (Module B (algebraModule F g : Type u))
    Algebra B (algebraCarrier F g) :=
  -- Local instance justification (proof-local temporary data): `Algebra.ofModule`
  -- requires the commutative ring structure induced by `h_tensor` and `h_unit`.
  letI := algebraCommRing F h_tensor h_unit g
  letI : Module B (algebraCarrier F g) :=
    inferInstanceAs (Module B (algebraModule F g : Type u))
  Algebra.ofModule sorry sorry

/-- Multiplication-by-`a` on the associated sheaf of `Γ(U.left, ⊤)`. -/
def associatedMulLeft (U : Over S) [IsAffine U.left] (a : Γ(U.left, ⊤)) :
    (associatedQCoh U).obj (ModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤)) ⟶
      (associatedQCoh U).obj (ModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤)) :=
  (associatedQCoh U).map (ModuleCat.ofHom (LinearMap.mulLeft Γ(U.left, ⊤) a))

/-- `associatedMulLeft a` is `associatedQCoh` of `mulLeft a`. -/
theorem associatedMulLeft_eq (U : Over S) [IsAffine U.left] (a : Γ(U.left, ⊤)) :
    associatedMulLeft U a =
      (associatedQCoh U).map (ModuleCat.ofHom (LinearMap.mulLeft Γ(U.left, ⊤) a)) :=
  rfl

/-- The identity object of `slice U`. -/
def sliceTerminal (U : Over S) : (GroupoidsOver.slice U).total :=
  Over.mk (𝟙 U)

/-- The ring map `A → O_U` at the identity object of `slice U`. -/
def associatedIdRingHom (U : Over S) :
    Γ(U.left, ⊤) →+*
      (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf.obj.obj
        (op (sliceTerminal U)) :=
  RingHom.id _

/-- The ring map `A → O(T)` on the fppf structure sheaf of `slice U`. -/
def associatedUnitRingHom (U : Over S)
    (x : (GroupoidsOver.slice U).totalᵒᵖ) :
    Γ(U.left, ⊤) →+*
      (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf.obj.obj x :=
  ((fppfRingedSite (GroupoidsOver.slice U)).structureSheaf.obj.map
      (Over.homMk x.unop.hom sorry).op).hom.comp (associatedIdRingHom U)

/-- Objectwise multiplication-by-`a` on the unit module of `slice U`. -/
def structureSheafMulLeft_module (U : Over S) (a : Γ(U.left, ⊤)) :
    (structureSheaf (GroupoidsOver.slice U)).obj ⟶
      (structureSheaf (GroupoidsOver.slice U)).obj where
  val.app x :=
    ModuleCat.homMk
      (AddCommGrpCat.ofHom
        { toFun := fun m ↦
            let m' : (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf.obj.obj x := m
            associatedUnitRingHom U x a * m'
          map_zero' := sorry
          map_add' := sorry })
      (fun _ ↦ sorry)
  val.naturality := sorry

/-- Multiplication-by-`a` on `O_U`, as an endomorphism of the quasi-coherent
structure sheaf. -/
def structureSheafMulLeft (U : Over S) (a : Γ(U.left, ⊤)) :
    structureSheaf (GroupoidsOver.slice U) ⟶
      structureSheaf (GroupoidsOver.slice U) :=
  homMk (structureSheafMulLeft_module U a)

/-- `structureSheafMulLeft` is the quasi-coherent packaging of objectwise
multiplication by `a`. -/
theorem structureSheafMulLeft_eq (U : Over S) (a : Γ(U.left, ⊤)) :
    structureSheafMulLeft U a = homMk (structureSheafMulLeft_module U a) :=
  rfl

/-- The ring map `A → C` sending `a` to `κ'(a)(1)`, where `κ'(a)` is `F` of the
pushforward of multiplication by `a` on `O_U`. -/
def structureRingHom (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅ ModuleCat.of B (F.obj M ⊗[B] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    -- Local instance justification (proof-local temporary data): the target ring
    -- structure of `algebraCarrier` is induced by `h_tensor` and `h_unit`.
    letI := algebraCommRing F h_tensor h_unit g
    Γ(U.left, ⊤) →+* algebraCarrier F g :=
  -- Local instance justification (proof-local temporary data): the target ring
  -- structure of `algebraCarrier` is induced by `h_tensor` and `h_unit`.
  letI := algebraCommRing F h_tensor h_unit g
  { toFun a :=
      (F.map ((directImage g).map (structureSheafMulLeft U a))).hom
        (algebraOne F h_unit g)
    map_one' := sorry
    map_mul' := sorry
    map_zero' := sorry
    map_add' := sorry }

/-- `structureRingHom` evaluates `F` of the pushforward of `mulLeft a` at the
unit of `C`. -/
theorem structureRingHom_spec (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅ ModuleCat.of B (F.obj M ⊗[B] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (a : Γ(U.left, ⊤)) :
    structureRingHom F h_tensor h_unit g a =
      (F.map ((directImage g).map (structureSheafMulLeft U a))).hom
        (algebraOne F h_unit g) :=
  rfl

/-- `C` is an algebra over `A = Γ(U.left, ⊤)` via `structureRingHom`. -/
@[reducible] def algebraOfA (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅ ModuleCat.of B (F.obj M ⊗[B] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    -- Local instance justification (proof-local temporary data): `toAlgebra`
    -- requires the commutative ring structure induced by `h_tensor` and `h_unit`.
    letI := algebraCommRing F h_tensor h_unit g
    Algebra Γ(U.left, ⊤) (algebraCarrier F g) :=
  -- Local instance justification (proof-local temporary data): `toAlgebra`
  -- requires the commutative ring structure induced by `h_tensor` and `h_unit`.
  letI := algebraCommRing F h_tensor h_unit g
  (structureRingHom F h_tensor h_unit g).toAlgebra

/-- The functor `M ↦ M ⊗[A] C` from `A`-modules to `B`-modules. -/
def tensoringAlong (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅ ModuleCat.of B (F.obj M ⊗[B] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    ModuleCat.{u} Γ(U.left, ⊤) ⥤ ModuleCat.{u} B :=
  -- Local instance justification (proof-local temporary data): extension and
  -- restriction of scalars along `A → C` and `B → C` use the ring/algebra
  -- structures induced by `h_tensor` and `h_unit`.
  letI := algebraCommRing F h_tensor h_unit g
  letI := algebraOfB F h_tensor h_unit g
  letI := algebraOfA F h_tensor h_unit g
  ModuleCat.extendScalars (structureRingHom F h_tensor h_unit g) ⋙
    ModuleCat.restrictScalars (algebraMap B (algebraCarrier F g))

/-- `tensoringAlong` is extension of scalars along `A → C` followed by
restriction of scalars along `B → C`. -/
theorem tensoringAlong_eq (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_tensor : ∀ M N : QCoh X,
      F.obj (tensor M N) ≅ ModuleCat.of B (F.obj M ⊗[B] F.obj N))
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    -- Local instance justification (proof-local temporary data): the comparison
    -- unpacks the same induced ring/algebra structures used by `tensoringAlong`.
    letI := algebraCommRing F h_tensor h_unit g
    -- Local instance justification (proof-local temporary data): the comparison
    -- unpacks the same induced ring/algebra structures used by `tensoringAlong`.
    letI := algebraOfB F h_tensor h_unit g
    -- Local instance justification (proof-local temporary data): the comparison
    -- unpacks the same induced ring/algebra structures used by `tensoringAlong`.
    letI := algebraOfA F h_tensor h_unit g
    tensoringAlong F h_tensor h_unit g =
      ModuleCat.extendScalars (structureRingHom F h_tensor h_unit g) ⋙
        ModuleCat.restrictScalars (algebraMap B (algebraCarrier F g)) :=
  -- Local instance justification (proof-local temporary data): the comparison
  -- unpacks the same induced ring/algebra structures used by `tensoringAlong`.
  letI := algebraCommRing F h_tensor h_unit g
  letI := algebraOfB F h_tensor h_unit g
  letI := algebraOfA F h_tensor h_unit g
  rfl

/-- The associated sheaf of the coordinate ring of an affine `U` is isomorphic
to the quasi-coherent structure sheaf of `slice U`. -/
theorem associatedQCoh_structureSheaf (U : Over S) [IsAffine U.left] :
    Nonempty
      ((associatedQCoh U).obj (ModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤)) ≅
        structureSheaf (GroupoidsOver.slice U)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
