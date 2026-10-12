/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap96.Lemma_96_15_1_Tensor
public import stacks_project.Chap96.Proposition_96_14_3_Comparison
public import stacks_project.Chap106.Lemma_106_16_5_Kunneth

/-!
# Affine tensor pullback of quasi-coherent modules

A morphism `f : Spec(B) ⟶ X` of an algebraic stack determines the tensor functor
`f* : QCoh(O_X) ⥤ ModuleCat B`, obtained by pulling back along `f` and evaluating
on the affine slice. A 2-arrow `f₁ ⟶ f₂` induces an isomorphism of these tensor
functors.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Functor CategoryTheory.ObjectProperty Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}}

/-- The identity object of `slice U`, playing the role of `Spec(B)` in the
fppf site of the slice. -/
def sliceId (U : Over S) : (GroupoidsOver.slice U).total :=
  Over.mk (𝟙 U)

/-- `sliceId U` is the identity morphism of `U`, as an object of `slice U`. -/
theorem sliceId_eq (U : Over S) : sliceId U = Over.mk (𝟙 U) :=
  rfl

/-- The ring map identifying `Γ(U.left, ⊤)` with the structure sheaf of
`slice U` at `sliceId U`. -/
def evalAffineRingHom (U : Over S) :
    Γ(U.left, ⊤) →+*
      (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf.obj.obj
        (op (sliceId U)) :=
  RingHom.id _

/-- `evalAffineRingHom U` is the identity ring homomorphism on global sections. -/
theorem evalAffineRingHom_eq (U : Over S) :
    evalAffineRingHom U = RingHom.id _ :=
  rfl

/-- Evaluation of a quasi-coherent module on the affine slice `U` at `sliceId U`,
as a functor to modules over `Γ(U.left, ⊤)`. -/
def evalAffine (U : Over S) [IsAffine U.left] :
    QCoh (GroupoidsOver.slice U) ⥤ ModuleCat.{u} Γ(U.left, ⊤) :=
  inclusion (GroupoidsOver.slice U) ⋙
    SheafOfModules.evaluation
      (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf (op (sliceId U)) ⋙
    ModuleCat.restrictScalars (evalAffineRingHom U)

/-- Objectwise, `evalAffine` evaluates at `sliceId U` and restricts scalars along
`evalAffineRingHom`. -/
theorem evalAffine_obj (U : Over S) [IsAffine U.left]
    (M : QCoh (GroupoidsOver.slice U)) :
    (evalAffine U).obj M =
      (ModuleCat.restrictScalars (evalAffineRingHom U)).obj
        ((SheafOfModules.evaluation
            (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf
            (op (sliceId U))).obj M.obj) :=
  rfl

/-- Morphisms are evaluated at `sliceId U` and then restricted along
`evalAffineRingHom`. -/
theorem evalAffine_map (U : Over S) [IsAffine U.left]
    {M N : QCoh (GroupoidsOver.slice U)} (φ : M ⟶ N) :
    (evalAffine U).map φ =
      (ModuleCat.restrictScalars (evalAffineRingHom U)).map
        ((SheafOfModules.evaluation
            (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf
            (op (sliceId U))).map φ.hom) :=
  rfl

/-- The tensor functor `f* : QCoh(O_X) ⥤ ModuleCat Γ(U.left, ⊤)` attached to a
morphism from an affine scheme. -/
def tensorPullback {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) :
    QCoh X ⥤ ModuleCat.{u} Γ(U.left, ⊤) :=
  pullback f ⋙ evalAffine U

/-- `tensorPullback f` is pullback along `f` followed by affine evaluation. -/
theorem tensorPullback_obj {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M : QCoh X) :
    (tensorPullback f).obj M = (evalAffine U).obj ((pullback f).obj M) :=
  rfl

/-- A 2-arrow `α : f₁ ⟶ f₂` induces an isomorphism of tensor functors
`f₁* ≅ f₂*`. -/
def tensorPullbackIso {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    [IsAffine U.left] {f1 f2 : GroupoidsOver.slice U ⟶ X} (α : f1 ⟶ f2) :
    tensorPullback f1 ≅ tensorPullback f2 :=
  isoWhiskerRight (pullbackIso (asIso α)).symm (evalAffine U)

/-- Components of `tensorPullbackIso α` are affine evaluation of
`(pullbackIso (asIso α)).symm`. -/
theorem tensorPullbackIso_hom_app {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] {f1 f2 : GroupoidsOver.slice U ⟶ X}
    (α : f1 ⟶ f2) (M : QCoh X) :
    (tensorPullbackIso α).hom.app M =
      (evalAffine U).map ((pullbackIso (asIso α)).inv.app M) :=
  rfl

/-- Affine evaluation of the structure sheaf of `slice U` is the regular module
`Γ(U.left, ⊤)`. -/
def evalAffine_structureSheaf (U : Over S) [IsAffine U.left] :
    (evalAffine U).obj (structureSheaf (GroupoidsOver.slice U)) ≅
      ModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤) :=
  (ModuleCat.restrictScalarsId' (evalAffineRingHom U) rfl).app
    ((SheafOfModules.evaluation
        (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf
        (op (sliceId U))).obj
      (structureSheaf (GroupoidsOver.slice U)).obj)

/-- `evalAffine_structureSheaf` is restriction of scalars along the identity
ring map, evaluated on the unit module. -/
theorem evalAffine_structureSheaf_eq (U : Over S) [IsAffine U.left] :
    evalAffine_structureSheaf U =
      (ModuleCat.restrictScalarsId' (evalAffineRingHom U) rfl).app
        ((SheafOfModules.evaluation
            (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf
            (op (sliceId U))).obj
          (structureSheaf (GroupoidsOver.slice U)).obj) :=
  rfl

/-- The QCoh-level structure-sheaf pullback isomorphism along `f`. -/
def structureSheafPullbackIso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (pullback f).obj (structureSheaf Y) ≅ structureSheaf X where
  hom := structureSheafPullbackInv f
  inv := structureSheafPullbackHom f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `structureSheafPullbackIso` is the inverse of `structureSheafPullbackHom`. -/
theorem structureSheafPullbackIso_hom {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (structureSheafPullbackIso f).hom = structureSheafPullbackInv f :=
  rfl

/-- The unit constraint of `f*`: pullback of `O_X` evaluates to `B`. -/
def tensorPullback_unit {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) :
    (tensorPullback f).obj (structureSheaf X) ≅
      ModuleCat.of Γ(U.left, ⊤) Γ(U.left, ⊤) :=
  (evalAffine U).mapIso (structureSheafPullbackIso f) ≪≫
    evalAffine_structureSheaf U

/-- `tensorPullback_unit` is affine evaluation of the structure-sheaf pullback
isomorphism, followed by evaluation of `O` on `slice U`. -/
theorem tensorPullback_unit_eq {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) :
    tensorPullback_unit f =
      (evalAffine U).mapIso (structureSheafPullbackIso f) ≪≫
        evalAffine_structureSheaf U :=
  rfl

/-- Affine evaluation of a quasi-coherent module, before restriction of scalars
along `evalAffineRingHom`. -/
def evalAffine_evaluationIso (U : Over S) [IsAffine U.left]
    (F : QCoh (GroupoidsOver.slice U)) :
    (evalAffine U).obj F ≅
      (SheafOfModules.evaluation
          (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf
          (op (sliceId U))).obj F.obj :=
  (ModuleCat.restrictScalarsId' (evalAffineRingHom U) rfl).app _

/-- `evalAffine_evaluationIso` is restriction of scalars along the identity. -/
theorem evalAffine_evaluationIso_eq (U : Over S) [IsAffine U.left]
    (F : QCoh (GroupoidsOver.slice U)) :
    evalAffine_evaluationIso U F =
      (ModuleCat.restrictScalarsId' (evalAffineRingHom U) rfl).app
        ((SheafOfModules.evaluation
            (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf
            (op (sliceId U))).obj F.obj) :=
  rfl

/-- The image of `sliceId U` along `f`, playing the role of the image of `Spec(B)` in
`X`. -/
def tensorPullback_image {X : GroupoidsOver S} {U : Over S}
    (f : GroupoidsOver.slice U ⟶ X) : X.total :=
  (toCartesianBasedFunctor f).toFunctor.obj (sliceId U)

/-- `tensorPullback_image f` is the total functor of `f` applied to `sliceId U`. -/
theorem tensorPullback_image_eq {X : GroupoidsOver S} {U : Over S}
    (f : GroupoidsOver.slice U ⟶ X) :
    tensorPullback_image f =
      (toCartesianBasedFunctor f).toFunctor.obj (sliceId U) :=
  rfl

/-- Evaluation of the inclusion comparison of `QCoh.pullback` at `sliceId`. -/
def pullback_evalIso {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M : QCoh X) :
    (SheafOfModules.evaluation
        (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf
        (op (sliceId U))).obj ((pullback f).obj M).obj ≅
      (SheafOfModules.evaluation
        (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf
        (op (sliceId U))).obj ((modulePullback f).obj M.obj) :=
  (SheafOfModules.evaluation
      (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf
      (op (sliceId U))).mapIso
    ((ObjectProperty.FullSubcategory.restrict.compιIso (modulePullback f)
        (modulePullback_le_inverseImage f)).app M)

/-- `pullback_evalIso` is evaluation of `restrict.compιIso`. -/
theorem pullback_evalIso_eq {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M : QCoh X) :
    pullback_evalIso f M =
      (SheafOfModules.evaluation
          (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf
          (op (sliceId U))).mapIso
        ((ObjectProperty.FullSubcategory.restrict.compιIso (modulePullback f)
            (modulePullback_le_inverseImage f)).app M) :=
  rfl

/-- Affine evaluation of `f* M` compared with evaluation of `modulePullback f`. -/
def tensorPullback_moduleEvalIso {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M : QCoh X) :
    (tensorPullback f).obj M ≅
      (SheafOfModules.evaluation
          (fppfRingedSite (GroupoidsOver.slice U)).structureSheaf
          (op (sliceId U))).obj ((modulePullback f).obj M.obj) :=
  evalAffine_evaluationIso U ((pullback f).obj M) ≪≫ pullback_evalIso f M

/-- `tensorPullback_moduleEvalIso` is affine evaluation followed by the inclusion
comparison of `QCoh.pullback`. -/
theorem tensorPullback_moduleEvalIso_eq {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M : QCoh X) :
    tensorPullback_moduleEvalIso f M =
      evalAffine_evaluationIso U ((pullback f).obj M) ≪≫ pullback_evalIso f M :=
  rfl

/-- Evaluation of `modulePullback f` is restriction of scalars of evaluation at
`f(sliceId)`. -/
def modulePullback_restrictEvalIso {X : GroupoidsOver S} {U : Over S}
    (f : GroupoidsOver.slice U ⟶ X)
    (M : SheafOfModules.{u} (GroupoidsOver.structureSheaf X)) :
    ((modulePullback f).obj M).val.obj (op (sliceId U)) ≅
      (ModuleCat.restrictScalars
          ((structureSheafMap f).hom.app (op (sliceId U))).hom).obj
        (M.val.obj (op (tensorPullback_image f))) :=
  Iso.refl _

/-- `modulePullback_restrictEvalIso` is the pushforward unfolding of
`modulePullback`. -/
theorem modulePullback_restrictEvalIso_eq {X : GroupoidsOver S} {U : Over S}
    (f : GroupoidsOver.slice U ⟶ X)
    (M : SheafOfModules.{u} (GroupoidsOver.structureSheaf X)) :
    modulePullback_restrictEvalIso f M = Iso.refl _ :=
  rfl

/-- Carrier of affine evaluation of `f* M`, named so that the `Γ(U.left, ⊤)`-module
instance does not unfold `evalAffine`. -/
abbrev tensorPullback_evalType {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M : QCoh X) :
    Type u :=
  (tensorPullback f).obj M

/-- `tensorPullback_evalType` is the underlying type of affine evaluation. -/
theorem tensorPullback_evalType_eq {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M : QCoh X) :
    tensorPullback_evalType f M = ((tensorPullback f).obj M : Type u) :=
  rfl

/-- Affine evaluation of `f* M` is an additive commutative group. -/
instance tensorPullback_evalType.addCommGroup {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S} [IsAffine U.left]
    (f : GroupoidsOver.slice U ⟶ X) (M : QCoh X) :
    AddCommGroup (tensorPullback_evalType f M) :=
  ModuleCat.isAddCommGroup ((tensorPullback f).obj M)

/-- Affine evaluation of `f* M` is a module over `Γ(U.left, ⊤)`. -/
instance tensorPullback_evalType.module {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M : QCoh X) :
    Module Γ(U.left, ⊤) (tensorPullback_evalType f M) :=
  ModuleCat.isModule ((tensorPullback f).obj M)

/-- Transport an affine evaluation of `f* M` to a commutative section of `M` at
`f(sliceId)`. -/
def tensorPullback_toCommSection {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M : QCoh X)
    (x : tensorPullback_evalType f M) :
    ((toCommFppfModules X).obj M.obj).val.obj (op (tensorPullback_image f)) :=
  ((modulePullback_restrictEvalIso f M.obj).hom
    ((tensorPullback_moduleEvalIso f M).hom x))

/-- Reverse transport from a commutative section of `M` at `f(sliceId)` to affine
evaluation of `f* M`. -/
def tensorPullback_ofCommSection {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M : QCoh X)
    (s : ((toCommFppfModules X).obj M.obj).val.obj (op (tensorPullback_image f))) :
    tensorPullback_evalType f M :=
  (tensorPullback_moduleEvalIso f M).inv
    ((modulePullback_restrictEvalIso f M.obj).inv s)

/-- Pure tensor of two commutative sections of `M` and `N` at `f(sliceId)`,
obtained from the already constructed universe-lifted bilinear comparison. -/
def tensorPullback_commTensorSection {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} (f : GroupoidsOver.slice U ⟶ X) (M N : QCoh X)
    (x : ((toCommFppfModules X).obj M.obj).val.obj (op (tensorPullback_image f)))
    (y : ((toCommFppfModules X).obj N.obj).val.obj (op (tensorPullback_image f))) :
    (moduleTensor M N).val.obj (op (tensorPullback_image f)) :=
  ((moduleTensorLiftBilinear
      ((toCommFppfModules X).obj M.obj)
      ((toCommFppfModules X).obj N.obj)).app
    (op (tensorPullback_image f)) (ULift.up x) (ULift.up y)).down

/-- Pure tensor of two affine evaluations, as a commutative section of `M ⊗ N` at
`f(sliceId)`. -/
def tensorPullback_tensorSection {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M N : QCoh X)
    (x : tensorPullback_evalType f M) (y : tensorPullback_evalType f N) :
    ((toCommFppfModules X).obj (tensor M N).obj).val.obj
      (op (tensorPullback_image f)) :=
  ((tensorComparison M N).val.app (op (tensorPullback_image f))).hom
    (tensorPullback_commTensorSection f M N
      (tensorPullback_toCommSection f M x)
      (tensorPullback_toCommSection f N y))

/-- The pairing of affine evaluations into evaluation of `f*(M ⊗ N)`. -/
def tensorPullback_tensorPair {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M N : QCoh X)
    (x : tensorPullback_evalType f M) (y : tensorPullback_evalType f N) :
    tensorPullback_evalType f (tensor M N) :=
  tensorPullback_ofCommSection f (tensor M N)
    (tensorPullback_tensorSection f M N x y)

/-- The bilinear pairing of affine evaluations into evaluation of `f*(M ⊗ N)`. -/
def tensorPullback_tensorBilinear {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M N : QCoh X) :
    tensorPullback_evalType f M →ₗ[Γ(U.left, ⊤)]
      tensorPullback_evalType f N →ₗ[Γ(U.left, ⊤)]
        tensorPullback_evalType f (tensor M N) :=
  LinearMap.mk₂ Γ(U.left, ⊤) (tensorPullback_tensorPair f M N)
    sorry sorry sorry sorry

/-- Reverse comparison from the module tensor of evaluations to evaluation of
`f*(M ⊗ N)`. -/
def tensorPullback_tensorInv {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M N : QCoh X) :
    ModuleCat.of Γ(U.left, ⊤)
        ((tensorPullback f).obj M ⊗[Γ(U.left, ⊤)] (tensorPullback f).obj N) ⟶
      (tensorPullback f).obj (tensor M N) :=
  let source : ModuleCat.{u} Γ(U.left, ⊤) :=
    ModuleCat.of Γ(U.left, ⊤)
      ((tensorPullback f).obj M ⊗[Γ(U.left, ⊤)] (tensorPullback f).obj N)
  let target : ModuleCat.{u} Γ(U.left, ⊤) := (tensorPullback f).obj (tensor M N)
  @ModuleCat.ofHom Γ(U.left, ⊤) _ (source : Type u) (target : Type u)
    (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
    (tensorPullback_evalType.addCommGroup f (tensor M N))
    (tensorPullback_evalType.module f (tensor M N))
    (TensorProduct.lift (tensorPullback_tensorBilinear f M N))

/-- `tensorPullback_tensorInv` is the tensor-product lift of
`tensorPullback_tensorBilinear`. -/
theorem tensorPullback_tensorInv_eq {X : GroupoidsOver S} [AlgebraicStack X]
    {U : Over S} [IsAffine U.left] (f : GroupoidsOver.slice U ⟶ X) (M N : QCoh X) :
    tensorPullback_tensorInv f M N =
      let source : ModuleCat.{u} Γ(U.left, ⊤) :=
        ModuleCat.of Γ(U.left, ⊤)
          ((tensorPullback f).obj M ⊗[Γ(U.left, ⊤)] (tensorPullback f).obj N)
      let target : ModuleCat.{u} Γ(U.left, ⊤) := (tensorPullback f).obj (tensor M N)
      @ModuleCat.ofHom Γ(U.left, ⊤) _ (source : Type u) (target : Type u)
        (ModuleCat.isAddCommGroup source) (ModuleCat.isModule source)
        (tensorPullback_evalType.addCommGroup f (tensor M N))
        (tensorPullback_evalType.module f (tensor M N))
        (TensorProduct.lift (tensorPullback_tensorBilinear f M N)) :=
  rfl

/-- An isomorphism of affine tensor functors is compatible with the tensor and
unit constraints of `f*`. -/
def IsTensorNatIso {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    [IsAffine U.left] {f1 f2 : GroupoidsOver.slice U ⟶ X}
    (t : tensorPullback f1 ≅ tensorPullback f2) : Prop :=
  (∀ M N : QCoh X,
      tensorPullback_tensorInv f1 M N ≫ t.hom.app (tensor M N) =
        ModuleCat.ofHom (TensorProduct.map (t.hom.app M).hom (t.hom.app N).hom) ≫
          tensorPullback_tensorInv f2 M N) ∧
    t.hom.app (structureSheaf X) ≫ (tensorPullback_unit f2).hom =
      (tensorPullback_unit f1).hom

/-- Tensor-naturality of `t` is the tensor square against
`tensorPullback_tensorInv` for all `M, N`, together with the unit square. -/
theorem IsTensorNatIso.iff {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    [IsAffine U.left] {f1 f2 : GroupoidsOver.slice U ⟶ X}
    (t : tensorPullback f1 ≅ tensorPullback f2) :
    IsTensorNatIso t ↔
      (∀ M N : QCoh X,
          tensorPullback_tensorInv f1 M N ≫ t.hom.app (tensor M N) =
            ModuleCat.ofHom (TensorProduct.map (t.hom.app M).hom (t.hom.app N).hom) ≫
              tensorPullback_tensorInv f2 M N) ∧
        t.hom.app (structureSheaf X) ≫ (tensorPullback_unit f2).hom =
          (tensorPullback_unit f1).hom :=
  Iff.rfl

/-- A 2-arrow induces a tensor-natural isomorphism of affine tensor functors. -/
theorem IsTensorNatIso.of_tensorPullbackIso {X : GroupoidsOver S}
    [AlgebraicStack X] {U : Over S} [IsAffine U.left]
    {f1 f2 : GroupoidsOver.slice U ⟶ X} (α : f1 ⟶ f2) :
    IsTensorNatIso (tensorPullbackIso α) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
