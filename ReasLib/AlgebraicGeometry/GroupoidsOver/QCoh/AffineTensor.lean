/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Associated
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Monoidal
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage.Tensor
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.SmallSections
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Affine
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-! # Pushforward algebras and affine tensor comparisons

A symmetric monoidal functor sends a quasi-coherent pushforward of a structure
module to an algebra on its original underlying module. For an affine source,
coordinate multiplication defines its coordinate-ring action and the canonical
comparison from scalar extension to evaluation of associated modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.MonoidalCategory SheafOfModules.RingedSite
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom (Affine)
open scoped Bicategory TensorProduct ChangeOfRings

noncomputable section

-- Public constructions retain private component formulas.
set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable {B : Type u} [CommRing B]

/-- The evaluated direct image of the structure module, with its original module structure. -/
def algebraModule (F : QCoh X ⥤ ModuleCat.{u} B)
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] : ModuleCat.{u} B :=
  F.obj ((directImage g).obj (structureSheaf Y))

/-- Multiplication on a direct image of the structure module is the cup product
followed by direct image of structure-module multiplication. -/
def directImageStructureSheafMul {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    Fppf.tensor ((directImage g).obj (structureSheaf Y))
        ((directImage g).obj (structureSheaf Y)) ⟶
      (directImage g).obj (structureSheaf Y) :=
  directImage_tensorComparison g (toLQCohFbcAdjunction X)
      (structureSheaf Y) (structureSheaf Y) ≫
    (directImage g).map (structureSheafMul Y)

/-- A specified tensor comparison induces a linear multiplication operation. -/
def algebraMulLinear (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_tensor : ∀ M N : QCoh X,
      F.obj (Fppf.tensor M N) ≅ ModuleCat.of B (F.obj M ⊗[B] F.obj N))
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    algebraModule F g ⊗[B] algebraModule F g →ₗ[B] algebraModule F g :=
  ((h_tensor ((directImage g).obj (structureSheaf Y))
      ((directImage g).obj (structureSheaf Y))).inv ≫
    F.map (directImageStructureSheafMul g)).hom

/-- The pushforward structure-module unit is induced by the pullback/direct-image adjunction. -/
def structureSheafDirectImageUnit {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    structureSheaf X ⟶ (directImage g).obj (structureSheaf Y) :=
  (pullbackDirectImageAdjunction g).unit.app (structureSheaf X) ≫
    (directImage g).map (structureSheafPullbackInv g)

/-- A specified unit comparison gives the evaluated pushforward unit. -/
def algebraOne (F : QCoh X ⥤ ModuleCat.{u} B)
    (h_unit : F.obj (structureSheaf X) ≅ ModuleCat.of B B)
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] : algebraModule F g :=
  (h_unit.inv ≫ F.map (structureSheafDirectImageUnit g)).hom (1 : B)

/-- A strong monoidal functor identifies the structure module with the coefficient module. -/
def tensorFunctorStructureSheafIso (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] :
    F.obj (structureSheaf X) ≅ ModuleCat.of B B :=
  F.mapIso ((quasiCoherentModuleProperty X).isoMk
    ((fromCommFppfModules X).mapIso
      (@unitIsoTensorUnit.{u + 1, u, u} X.total inferInstance
        (X.associatedTopology .fppf)
        (associatedTopology_hasSheafCompose_commRing X .fppf)
        (associatedTopology_hasWeakSheafify X .fppf)
        (associatedTopology_wEqualsLocallyBijective X .fppf)
        (commAssociatedStructureSheaf X .fppf)) ≪≫
      (Functor.Monoidal.εIso (fromCommFppfModules X)).symm)) ≪≫
    (Functor.Monoidal.εIso F).symm

private def canonicalMul (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided]
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (c d : algebraModule F g) : algebraModule F g :=
  algebraMulLinear F (fun M N ↦ (Functor.Monoidal.μIso F M N).symm) g (c ⊗ₜ[B] d)

/-- The canonical pushforward multiplication and unit satisfy the commutative-ring laws. -/
theorem algebraCommRing_laws (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided]
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    let mul := canonicalMul F g
    let one := algebraOne F (tensorFunctorStructureSheafIso F) g
    (∀ a b c, mul (mul a b) c = mul a (mul b c)) ∧
    (∀ a, mul one a = a) ∧ (∀ a, mul a one = a) ∧
    (∀ a, mul 0 a = 0) ∧ (∀ a, mul a 0 = 0) ∧
    (∀ a b c, mul a (b + c) = mul a b + mul a c) ∧
    (∀ a b c, mul (a + b) c = mul a c + mul b c) ∧
    (∀ a b, mul a b = mul b a) := sorry

/-- The commutative ring on the evaluated pushforward retains its given additive group. -/
@[reducible] def algebraCommRing (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided]
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    CommRing (algebraModule F g) where
  __ := (inferInstance : AddCommGroup (algebraModule F g))
  mul := canonicalMul F g
  one := algebraOne F (tensorFunctorStructureSheafIso F) g
  mul_assoc := (algebraCommRing_laws F g).1
  one_mul := (algebraCommRing_laws F g).2.1
  mul_one := (algebraCommRing_laws F g).2.2.1
  zero_mul := (algebraCommRing_laws F g).2.2.2.1
  mul_zero := (algebraCommRing_laws F g).2.2.2.2.1
  left_distrib := (algebraCommRing_laws F g).2.2.2.2.2.1
  right_distrib := (algebraCommRing_laws F g).2.2.2.2.2.2.1
  mul_comm := (algebraCommRing_laws F g).2.2.2.2.2.2.2

/-- The original coefficient action is compatible with canonical pushforward multiplication. -/
theorem algebraOfB_laws (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided]
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    (∀ (r : B) (c d : algebraModule F g),
      canonicalMul F g (r • c) d = r • canonicalMul F g c d) ∧
    (∀ (r : B) (c d : algebraModule F g),
      canonicalMul F g c (r • d) = r • canonicalMul F g c d) := sorry

/-- The coefficient algebra uses the unchanged action on the evaluated module. -/
@[reducible] def algebraOfB (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided]
    {Y : GroupoidsOver S} [AlgebraicStack Y] (g : Y ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    @Algebra B (algebraModule F g) inferInstance (algebraCommRing F g).toSemiring :=
  @Algebra.ofModule B (algebraModule F g) inferInstance
    (algebraCommRing F g).toSemiring (inferInstance : Module B (algebraModule F g))
    (algebraOfB_laws F g).1 (algebraOfB_laws F g).2

private def coordinateFunction (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (a : Γ(U.left, ⊤)) : algebraModule F g :=
  (F.map ((directImage g).map (structureSheafMulLeft U a))).hom
    (algebraOne F (tensorFunctorStructureSheafIso F) g)

/-- Evaluation of coordinate multiplication at the unit preserves ring operations. -/
theorem structureRingHom_laws (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    (coordinateFunction F g 1 = algebraOne F (tensorFunctorStructureSheafIso F) g) ∧
    (∀ a b, coordinateFunction F g (a * b) =
      canonicalMul F g (coordinateFunction F g a) (coordinateFunction F g b)) ∧
    (coordinateFunction F g 0 = 0) ∧
    (∀ a b, coordinateFunction F g (a + b) =
      coordinateFunction F g a + coordinateFunction F g b) := sorry

/-- The coordinate homomorphism evaluates pushforward multiplication by a coordinate at the unit. -/
def structureRingHom (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    @RingHom Γ(U.left, ⊤) (algebraModule F g) inferInstance
      (algebraCommRing F g).toNonAssocSemiring :=
  @RingHom.mk Γ(U.left, ⊤) (algebraModule F g) inferInstance
    (algebraCommRing F g).toNonAssocSemiring
    (@MonoidHom.mk Γ(U.left, ⊤) (algebraModule F g) inferInstance
      (algebraCommRing F g).toMulOne
      (@OneHom.mk Γ(U.left, ⊤) (algebraModule F g) inferInstance
        (algebraCommRing F g).toOne (coordinateFunction F g)
        (structureRingHom_laws F g).1)
      (structureRingHom_laws F g).2.1)
    (structureRingHom_laws F g).2.2.1 (structureRingHom_laws F g).2.2.2

/-- The coordinate-ring homomorphism has the specified evaluation formula. -/
theorem structureRingHom_spec (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (a : Γ(U.left, ⊤)) :
    structureRingHom F g a =
      (F.map ((directImage g).map (structureSheafMulLeft U a))).hom
        (algebraOne F (tensorFunctorStructureSheafIso F) g) := rfl

/-- The evaluated pushforward is a coordinate-ring algebra through its coordinate homomorphism. -/
@[reducible] def algebraOfA (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    @Algebra Γ(U.left, ⊤) (algebraModule F g) inferInstance
      (algebraCommRing F g).toSemiring :=
  @RingHom.toAlgebra Γ(U.left, ⊤) (algebraModule F g) inferInstance
    (algebraCommRing F g).toCommSemiring (structureRingHom F g)

/-- Extension along the coordinate homomorphism followed by restriction to the coefficient ring. -/
def tensoringAlong (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    ModuleCat.{u} Γ(U.left, ⊤) ⥤ ModuleCat.{u} B :=
  -- Local instance justification (noncanonical choice): the induced ring and algebra on this fixed module depend on F and g and have no global coherent instance; this scope only supplies Mathlib scalar-extension constructors.
  letI := algebraCommRing F g
  -- Local instance justification (noncanonical choice): the induced ring and algebra on this fixed module depend on F and g and have no global coherent instance; this scope only supplies Mathlib scalar-extension constructors.
  letI := algebraOfB F g
  ModuleCat.extendScalars (structureRingHom F g) ⋙
    ModuleCat.restrictScalars (algebraMap B (algebraModule F g))

/-- The tensor functor is precisely the specified extension and restriction of scalars. -/
theorem tensoringAlong_eq (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    -- Local instance justification (noncanonical choice): the induced ring and algebra on this fixed module depend on F and g and have no global coherent instance; this scope only supplies Mathlib scalar-extension constructors.
    letI := algebraCommRing F g
    -- Local instance justification (noncanonical choice): the induced ring and algebra on this fixed module depend on F and g and have no global coherent instance; this scope only supplies Mathlib scalar-extension constructors.
    letI := algebraOfB F g
    tensoringAlong F g =
      ModuleCat.extendScalars (structureRingHom F g) ⋙
        ModuleCat.restrictScalars (algebraMap B (algebraModule F g)) := rfl

private def comparisonPure (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (M : ModuleCat.{u} Γ(U.left, ⊤)) (c : algebraModule F g) (m : M) :
    (associatedQCoh U ⋙ directImage g ⋙ F).obj M :=
  ((associatedQCoh U ⋙ directImage g ⋙ F).map
    (ModuleCat.ofHom (LinearMap.toSpanSingleton Γ(U.left, ⊤) M m))).hom
      ((F.map ((directImage g).map (associatedQCohStructureSheafIso U).inv)).hom c)

/-- The pure-tensor comparison is biadditive, balanced over coordinates, and linear in coefficients. -/
theorem affineTensorComparisonApp_laws (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (M : ModuleCat.{u} Γ(U.left, ⊤)) :
    (∀ c d m, comparisonPure F g M (c + d) m =
      comparisonPure F g M c m + comparisonPure F g M d m) ∧
    (∀ c m n, comparisonPure F g M c (m + n) =
      comparisonPure F g M c m + comparisonPure F g M c n) ∧
    (∀ (a : Γ(U.left, ⊤)) c m,
      comparisonPure F g M (canonicalMul F g (structureRingHom F g a) c) m =
        comparisonPure F g M c (a • m)) ∧
    -- Local instance justification (noncanonical choice): the induced ring and algebra on this fixed module depend on F and g and have no global coherent instance; this scope only supplies Mathlib scalar-extension constructors.
    (letI := algebraCommRing F g
     ∀ (φ : (tensoringAlong F g).obj M →+ (associatedQCoh U ⋙ directImage g ⋙ F).obj M),
       (∀ (c : algebraModule F g) (m : M),
         φ (c ⊗ₜ[Γ(U.left, ⊤), structureRingHom F g] m) = comparisonPure F g M c m) →
       ∀ (b : B) (t : (tensoringAlong F g).obj M), φ (b • t) = b • φ t) := sorry

private def comparisonAddHom (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (M : ModuleCat.{u} Γ(U.left, ⊤)) :
    algebraModule F g →+ M →+ (associatedQCoh U ⋙ directImage g ⋙ F).obj M :=
  AddMonoidHom.mk' (fun c ↦ AddMonoidHom.mk' (comparisonPure F g M c)
    ((affineTensorComparisonApp_laws F g M).2.1 c))
    (fun c d ↦ AddMonoidHom.ext ((affineTensorComparisonApp_laws F g M).1 c d))

/-- The canonical comparison on scalar extension, induced by maps from the free rank-one module. -/
def affineTensorComparisonApp (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (M : ModuleCat.{u} Γ(U.left, ⊤)) :
    (tensoringAlong F g).obj M ⟶ (associatedQCoh U ⋙ directImage g ⋙ F).obj M := by
  -- Local instance justification (noncanonical choice): the induced ring and algebra on this fixed module depend on F and g and have no global coherent instance; this scope only supplies Mathlib scalar-extension constructors.
  letI := algebraCommRing F g
  -- Local instance justification (noncanonical choice): the induced ring and algebra on this fixed module depend on F and g and have no global coherent instance; this scope only supplies Mathlib scalar-extension constructors.
  letI := algebraOfA F g
  let f : (tensoringAlong F g).obj M →+ (associatedQCoh U ⋙ directImage g ⋙ F).obj M :=
    TensorProduct.liftAddHom (comparisonAddHom F g M)
      ((affineTensorComparisonApp_laws F g M).2.2.1)
  exact ModuleCat.ofHom (X := (tensoringAlong F g).obj M)
    (Y := (associatedQCoh U ⋙ directImage g ⋙ F).obj M)
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun b t ↦
        (affineTensorComparisonApp_laws F g M).2.2.2 f (fun c m ↦ rfl) b t }

/-- On pure tensors the comparison evaluates the functor on the corresponding rank-one map. -/
theorem affineTensorComparisonApp_tmul (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    (M : ModuleCat.{u} Γ(U.left, ⊤)) (c : algebraModule F g) (m : M) :
    -- Local instance justification (noncanonical choice): the induced ring and algebra on this fixed module depend on F and g and have no global coherent instance; this scope only supplies Mathlib scalar-extension constructors.
    letI := algebraCommRing F g
    affineTensorComparisonApp F g M (c ⊗ₜ[Γ(U.left, ⊤), structureRingHom F g] m) =
      ((associatedQCoh U ⋙ directImage g ⋙ F).map
        (ModuleCat.ofHom (LinearMap.toSpanSingleton Γ(U.left, ⊤) M m))).hom
        ((F.map ((directImage g).map (associatedQCohStructureSheafIso U).inv)).hom c) := rfl

/-- The canonical scalar-extension comparison is natural in the coordinate-ring module. -/
theorem affineTensorComparison_naturality (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    {M N : ModuleCat.{u} Γ(U.left, ⊤)} (f : M ⟶ N) :
    (tensoringAlong F g).map f ≫ affineTensorComparisonApp F g N =
      affineTensorComparisonApp F g M ≫ (associatedQCoh U ⋙ directImage g ⋙ F).map f := sorry

/-- The natural comparison from tensoring with the evaluated algebra to evaluated associated modules. -/
def affineTensorComparison (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided] [PreservesFiniteColimits F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    tensoringAlong F g ⟶ associatedQCoh U ⋙ directImage g ⋙ F where
  app := affineTensorComparisonApp F g
  naturality _ _ f := affineTensorComparison_naturality F g f

/-- A right exact symmetric monoidal functor preserving direct sums evaluates
affine pushforwards by extension of scalars to their evaluated structure algebra. -/
instance affineTensorFunctor
    [Affine (diagonal.{u + 1, u, u + 1} X)]
    (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided]
    [PreservesFiniteColimits F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g] :
    IsIso (affineTensorComparison F g) := sorry

end AlgebraicGeometry.GroupoidsOver.QCoh

