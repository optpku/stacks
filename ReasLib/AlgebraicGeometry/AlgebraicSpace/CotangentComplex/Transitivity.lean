module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Sites.Adjunction
public import ReasLib.CategoryTheory.Sites.AlgebraicSheaf.FreeAlgebra
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Differentials.Conormal
public import ReasLib.CategoryTheory.Adjunction.Iteration
public import ReasLib.CategoryTheory.Adjunction.SimplicialResolution.Construction
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Natural
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingInverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRing
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.CategoryTheory.Sites.Sheafification.Abelian
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PullbackMixedUniverse
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Transitivity of cotangent complexes of algebraic spaces

For composable morphisms `W ⟶ X ⟶ B` of algebraic spaces over a scheme `S`, this module
owns the cochain and derived cotangent complexes `L_{X/B}`, `Lp^* L_{X/B}`, and `L_{W/X}`,
together with the first two maps of the transitivity triangle in `D(O_W)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalCommRing
open CategoryTheory.Sheaf.InternalRing
open CochainComplex
open HomologicalComplex
open ComplexShape
open Opposite
open AlgebraicTopology
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open scoped Simplicial ZeroObject CategoryTheory.IteratedEndofunctor
open CategoryTheory.Sheaf.FreeAlgebra

-- Public constructions retain private component maps and proof laws.
set_option backward.privateInPublic true

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent

variable {S : Scheme.{u}}

/-- Sheaf composition along `forget CommRingCat.{u + 1}` on the small étale site. -/
instance hasSheafCompose_forget_commRing_succ (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose (CategoryTheory.forget CommRingCat.{u + 1}) :=
  sorry

/-- Restriction of scalars of `u + 1` module sheaves on the small étale site is a right adjoint. -/
instance restrictScalars_isRightAdjoint_succ (X : AlgebraicSpace S)
    {R R' : Sheaf (smallEtaleTopology X) RingCat.{u + 1}} (α : R ⟶ R') :
    (SheafOfModules.restrictScalars.{u + 1} α).IsRightAdjoint := by
  exact ((@SheafOfModules.PullbackConstruction.adjunction
    (smallEtaleSite X) _ (smallEtaleSite X) _
    (smallEtaleTopology X) (smallEtaleTopology X) (𝟭 _) R R' _
    (SheafOfModules.ChangeOfRings.homOverId α)
    (PresheafOfModules.MixedUniversePullback.isRightAdjoint _)
    (CategoryTheory.hasWeakSheafify_addCommGrp (smallEtaleTopology X)) _).ofNatIsoRight
      (SheafOfModules.ChangeOfRings.pushforwardIso α)).isRightAdjoint

/-- Sheaf composition along `forget₂ CommRingCat RingCat` on the small étale site. -/
instance hasSheafCompose_forget₂_commRing_succ (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

/-- Weak sheafification of lifted commutative ring sheaves on the small étale site. -/
instance hasWeakSheafify_commRing_succ (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) CommRingCat.{u + 1} := by
  let hcolim : ∀ U : smallEtaleSite X,
      PreservesColimitsOfShape ((smallEtaleTopology X).Cover U)ᵒᵖ
        (CategoryTheory.forget CommRingCat.{u + 1}) := fun U ↦
    @PreservesFilteredColimitsOfSize.preserves_filtered_colimits _ _ _ _
      (CategoryTheory.forget CommRingCat.{u + 1}) inferInstance _ _
      (@isFiltered_op_of_isCofiltered _ _
        (isCofiltered_of_semilatticeInf_nonempty ((smallEtaleTopology X).Cover U)))
  exact (@plusPlusAdjunction _ _ (smallEtaleTopology X) CommRingCat.{u + 1}
    _ _ _ _ _ _ _ _ hcolim _).isRightAdjoint

/-- Binary coproducts of lifted commutative ring sheaves on the small étale site. -/
instance (priority := high) sheafCommRing_succ_hasBinaryCoproducts (X : AlgebraicSpace S) :
    HasColimitsOfShape (Discrete WalkingPair)
      (Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) :=
  @Sheaf.instHasColimitsOfShape _ _ (smallEtaleTopology X) CommRingCat.{u + 1} _
    (Discrete WalkingPair) _ (hasWeakSheafify_commRing_succ X) inferInstance

/-- The underlying ring sheaf of a lifted commutative-ring sheaf. -/
abbrev ringOf {X : AlgebraicSpace S}
    (𝒪 : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) :
    Sheaf (smallEtaleTopology X) RingCat.{u + 1} :=
  (sheafCompose (smallEtaleTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj 𝒪

/-- The underlying ring-sheaf morphism of a morphism of lifted commutative-ring sheaves. -/
abbrev ringOfMap {X : AlgebraicSpace S}
    {𝒪 𝒪' : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (α : 𝒪 ⟶ 𝒪') :
    ringOf 𝒪 ⟶ ringOf 𝒪' :=
  (sheafCompose (smallEtaleTopology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α

/-- Universe lift of a commutative-ring presheaf on the small étale site. -/
def liftPresheaf (X : AlgebraicSpace S)
    (P : (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u}) :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  P ⋙ CommRingCat.universeLift.{u, u + 1}

/-- The universe lift of a commutative-ring sheaf remains a sheaf. -/
theorem liftPresheaf_isSheaf (X : AlgebraicSpace S)
    (R : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    Presheaf.IsSheaf (smallEtaleTopology X) (liftPresheaf X R.obj) :=
  sorry

/-- Universe lift of a commutative-ring sheaf on the small étale site. -/
def liftSheafObj (X : AlgebraicSpace S)
    (R : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  ⟨liftPresheaf X R.obj, liftPresheaf_isSheaf X R⟩

/-- Naturality of the universe lift of a morphism of commutative-ring sheaves. -/
theorem liftSheafMap_naturality (X : AlgebraicSpace S)
    {R R' : Sheaf (smallEtaleTopology X) CommRingCat.{u}} (α : R ⟶ R')
    {U V : (smallEtaleSite X)ᵒᵖ} (f : U ⟶ V) :
    (liftPresheaf X R.obj).map f ≫
        (CommRingCat.universeLift.{u, u + 1}).map (α.hom.app V) =
      (CommRingCat.universeLift.{u, u + 1}).map (α.hom.app U) ≫
        (liftPresheaf X R'.obj).map f :=
  sorry

/-- Universe lift of a morphism of commutative-ring sheaves. -/
def liftSheafMap (X : AlgebraicSpace S)
    {R R' : Sheaf (smallEtaleTopology X) CommRingCat.{u}} (α : R ⟶ R') :
    liftSheafObj X R ⟶ liftSheafObj X R' :=
  ObjectProperty.homMk
    { app := fun U ↦ (CommRingCat.universeLift.{u, u + 1}).map (α.hom.app U)
      naturality := fun _ _ f ↦ liftSheafMap_naturality X α f }

/-- The universe lift preserves identity morphisms. -/
theorem liftSheafMap_id (X : AlgebraicSpace S)
    (R : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    liftSheafMap X (𝟙 R) = 𝟙 (liftSheafObj X R) :=
  sorry

/-- The universe lift preserves composition. -/
theorem liftSheafMap_comp (X : AlgebraicSpace S)
    {R R' R'' : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (α : R ⟶ R') (β : R' ⟶ R'') :
    liftSheafMap X (α ≫ β) = liftSheafMap X α ≫ liftSheafMap X β :=
  sorry

/-- Modules over the universe-lifted commutative structure sheaf of an algebraic space. -/
abbrev CommModules (X : AlgebraicSpace S) :=
  SheafOfModules.{u + 1} (ringOf (commStructureSheafLift X))

/-- The lifted module category of an algebraic space is abelian. -/
instance commModulesAbelian (X : AlgebraicSpace S) : Abelian (CommModules X) :=
  inferInstance

/-- The standard derived category of lifted `𝒪_X`-modules. -/
instance commModulesHasDerivedCategory (X : AlgebraicSpace S) :
    HasDerivedCategory (CommModules X) :=
  HasDerivedCategory.standard (CommModules X)

/-- The free-forgetful adjunction for lifted commutative algebra sheaves. -/
def freeForgetAdjunction {X : AlgebraicSpace S}
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) :
    Sheaf.composeAndSheafify (smallEtaleTopology X) CommRingCat.free ⋙ Under.costar A ⊣
      Under.forget A ⋙
        sheafCompose (smallEtaleTopology X) (CategoryTheory.forget CommRingCat.{u + 1}) :=
  (Sheaf.adjunction (smallEtaleTopology X) CommRingCat.adj).comp (Under.costarAdjForget A)

/-- The free-forgetful comonad endofunctor on lifted algebras under a fixed base sheaf. -/
def freeForgetEndo {X : AlgebraicSpace S}
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) :
    Under A ⥤ Under A :=
  Under.forget A ⋙
    sheafCompose (smallEtaleTopology X) (CategoryTheory.forget CommRingCat.{u + 1}) ⋙
      Sheaf.composeAndSheafify (smallEtaleTopology X) CommRingCat.free ⋙
        Under.costar A

/-- The degree-`n` algebra of the standard resolution of `B` over `A`. -/
abbrev standardTerm {X : AlgebraicSpace S}
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) : Under A :=
  (Endofunctor.iterate (freeForgetEndo A) (n.unop.len + 1)).obj B

/-- The augmentation from a standard-resolution term to the resolved algebra sheaf. -/
abbrev standardAugmentation {X : AlgebraicSpace S}
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) (B : Under A)
    (n : SimplexCategoryᵒᵖ) :
    (standardTerm A B n).right ⟶ B.right :=
  (Endofunctor.iterate.fold (freeForgetEndo A)
      ((freeForgetAdjunction A).counit.app B) (n.unop.len + 1)).right

/-- The morphism of standard-resolution terms induced by a simplex operator. -/
def standardMap {X : AlgebraicSpace S}
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) (B : Under A)
    {n m : SimplexCategoryᵒᵖ} (s : n ⟶ m) :
    standardTerm A B n ⟶ standardTerm A B m :=
  (EndofunctorResolution.simplicial.map (freeForgetAdjunction A).counit
      (freeForgetAdjunction A).toComonad.δ s).app B

/-- Extension of scalars of lifted module sheaves along a morphism of lifted ring sheaves. -/
abbrev extendAlong {X : AlgebraicSpace S}
    {O₀ O₁ : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (α : O₀ ⟶ O₁) :
    SheafOfModules.{u + 1} (ringOf O₀) ⥤ SheafOfModules.{u + 1} (ringOf O₁) :=
  SheafOfModules.ChangeOfRings.extendScalars (ringOfMap α)

/-- Extension of scalars of lifted module sheaves is left adjoint to restriction of scalars. -/
def extendRestrictAdj {X : AlgebraicSpace S}
    {O₀ O₁ : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (α : O₀ ⟶ O₁) :
    extendAlong α ⊣ SheafOfModules.restrictScalars (ringOfMap α) :=
  SheafOfModules.ChangeOfRings.extendRestrictAdjunction (ringOfMap α)

/-- Relative differentials of a morphism of lifted commutative ring sheaves on the small étale
site. -/
abbrev differentialsOn {X : AlgebraicSpace S}
    {O₀ O₁ : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (φ : O₀ ⟶ O₁) :
    SheafOfModules.{u + 1} (ringOf O₁) :=
  @relativeDifferentials.{u + 1, u, u + 1} (smallEtaleSite X) _ (smallEtaleTopology X) _
    (CategoryTheory.hasWeakSheafify_addCommGrp (smallEtaleTopology X)) _ _ _ φ

/-- Restriction of lifted module sheaves along a morphism of lifted ring sheaves. -/
abbrev restrictAlong {X : AlgebraicSpace S}
    {O₀ O₁ : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (α : O₀ ⟶ O₁) :
    SheafOfModules.{u + 1} (ringOf O₁) ⥤ SheafOfModules.{u + 1} (ringOf O₀) :=
  SheafOfModules.restrictScalars (ringOfMap α)

/-- The universe-lifted inverse-image structure sheaf `h⁻¹ 𝒪_Y`. -/
abbrev inverseImageLift {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u + 1} :=
  liftSheafObj X (commInverseImageStructureSheaf h)

/-- The lifted structure map `h♯ : h⁻¹ 𝒪_Y ⟶ 𝒪_X`. -/
def structureMapLift {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    inverseImageLift h ⟶ commStructureSheafLift X :=
  ObjectProperty.homMk
    { app := fun U ↦
        (CommRingCat.universeLift.{u, u + 1}).map
          ((commInverseImageStructureSheafMap h).hom.app U)
      naturality := fun _ _ f ↦
        liftSheafMap_naturality X (commInverseImageStructureSheafMap h) f }

/-- The pulled-back inverse-image sheaf `p⁻¹(f⁻¹ 𝒪_B)`. -/
abbrev pulledInverseImage {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    Sheaf (smallEtaleTopology W) CommRingCat.{u + 1} :=
  liftSheafObj W (commSheafInverseImageObj p (commInverseImageStructureSheaf f))

/-- The pulled-back structure map `p⁻¹(f♯) : p⁻¹(f⁻¹ 𝒪_B) ⟶ p⁻¹ 𝒪_X`. -/
def pulledMap {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    pulledInverseImage p f ⟶ inverseImageLift p :=
  liftSheafMap W (commSheafInverseImageMap p (commInverseImageStructureSheafMap f))

/-- The structure morphism of a standard-resolution term is compatible with a simplex operator. -/
theorem standardMap_w {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B : Under A}
    {n m : SimplexCategoryᵒᵖ} (s : n ⟶ m) :
    (standardTerm A B n).hom ≫ (standardMap A B s).right =
      (standardTerm A B m).hom :=
  sorry

/-- Forgetting commutativity identifies the two successive restriction paths of a simplex
operator. -/
theorem standardMap_comp_augmentation_ring {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B : Under A}
    {n m : SimplexCategoryᵒᵖ} (s : n ⟶ m) :
    ringOfMap (standardAugmentation A B n) =
      ringOfMap (standardMap A B s).right ≫ ringOfMap (standardAugmentation A B m) :=
  sorry

/-- The map of relative differentials induced by a simplex operator of the standard
resolution. -/
def simplicialDifferentialsMap {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B : Under A}
    {n m : SimplexCategoryᵒᵖ} (s : n ⟶ m) :
    differentialsOn (standardTerm A B n).hom ⟶
      (restrictAlong (standardMap A B s).right).obj
        (differentialsOn (standardTerm A B m).hom) :=
  @RelativeDifferentials.map.{u + 1, u, u + 1} (smallEtaleSite X) _
      (smallEtaleTopology X) _
      (CategoryTheory.hasWeakSheafify_addCommGrp (smallEtaleTopology X)) _ _ _ _ _ _ _ _ _
    ⟨(Category.id_comp (standardTerm A B m).hom).trans (standardMap_w s).symm⟩

/-- The map of `B`-modules induced by a simplicial operator of the standard resolution. -/
def simplicialModuleMap {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B : Under A}
    {n m : SimplexCategoryᵒᵖ} (s : n ⟶ m) :
    (extendAlong (standardAugmentation A B n)).obj
      (differentialsOn (standardTerm A B n).hom) ⟶
    (extendAlong (standardAugmentation A B m)).obj
      (differentialsOn (standardTerm A B m).hom) :=
  ((extendRestrictAdj (standardAugmentation A B n)).homEquiv _ _).symm
    (simplicialDifferentialsMap s ≫
      (restrictAlong (standardMap A B s).right).map
        ((extendRestrictAdj (standardAugmentation A B m)).unit.app _) ≫
      (SheafOfModules.Restriction.compIso'
          (ringOfMap (standardMap A B s).right)
          (ringOfMap (standardAugmentation A B m))
          (ringOfMap (standardAugmentation A B n))
          (standardMap_comp_augmentation_ring s)).hom.app _)

/-- The identity simplicial operator acts as the identity on the associated module. -/
theorem simplicialModuleMap_id {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B : Under A}
    (n : SimplexCategoryᵒᵖ) :
    simplicialModuleMap (X := X) (A := A) (B := B) (𝟙 n) =
      𝟙 ((extendAlong (standardAugmentation A B n)).obj
        (differentialsOn (standardTerm A B n).hom)) :=
  sorry

/-- Simplicial-operator composition is preserved by the associated module maps. -/
theorem simplicialModuleMap_comp {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B : Under A}
    {n m k : SimplexCategoryᵒᵖ} (s : n ⟶ m) (t : m ⟶ k) :
    simplicialModuleMap (X := X) (A := A) (B := B) (s ≫ t) =
      simplicialModuleMap (X := X) (A := A) (B := B) s ≫
        simplicialModuleMap (X := X) (A := A) (B := B) t :=
  sorry

/-- The simplicial `B`-module `Ω_{P_•/A} ⊗_{P_•} B` attached to the standard resolution. -/
def simplicialModule {X : AlgebraicSpace S}
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) (B : Under A) :
    SimplicialObject (SheafOfModules.{u + 1} (ringOf B.right)) where
  obj n := (extendAlong (standardAugmentation A B n)).obj
    (differentialsOn (standardTerm A B n).hom)
  map s := simplicialModuleMap s
  map_id n := simplicialModuleMap_id n
  map_comp s t := simplicialModuleMap_comp s t

/-- The cotangent complex of a morphism of lifted commutative ring sheaves, as the
alternating-face cochain complex of the standard-resolution simplicial module. -/
def cotangentCochainObj {X : AlgebraicSpace S}
    {O₀ O₁ : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (α : O₀ ⟶ O₁) :
    CochainComplex (SheafOfModules.{u + 1} (ringOf O₁)) ℤ :=
  ((alternatingFaceMapComplex (SheafOfModules.{u + 1} (ringOf O₁))).obj
      (simplicialModule O₀ (Under.mk α))).extend embeddingDownNat

/-- The cohomological degree `-n` term of a sheaf-level cotangent complex. -/
def cotangentXIso {X : AlgebraicSpace S}
    {O₀ O₁ : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (α : O₀ ⟶ O₁) (n : ℕ) :
    (cotangentCochainObj α).X (-n) ≅ (simplicialModule O₀ (Under.mk α)).obj (op ⦋n⦌) :=
  extendXIso
    ((alternatingFaceMapComplex (SheafOfModules.{u + 1} (ringOf O₁))).obj
      (simplicialModule O₀ (Under.mk α)))
    embeddingDownNat rfl

/-- The cotangent complex `L_{X/Y}` of a morphism of algebraic spaces, as a cochain complex
of lifted `𝒪_X`-modules. -/
def cotangentCochain {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    CochainComplex (CommModules X) ℤ :=
  cotangentCochainObj (structureMapLift h)

/-- Unfolding of `cotangentCochain` as the sheaf-level cotangent of `h♯`. -/
theorem cotangentCochain_eq {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    cotangentCochain h = cotangentCochainObj (structureMapLift h) :=
  rfl

/-- The cotangent complex `L_{X/Y}` of a morphism of algebraic spaces, as an object of
`D(𝒪_X)`. -/
def cotangent {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    DerivedCategory (CommModules X) :=
  DerivedCategory.Q.obj (cotangentCochain h)

/-- Unfolding of `cotangent` as `DerivedCategory.Q` of `cotangentCochain`. -/
theorem cotangent_eq {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    cotangent h = DerivedCategory.Q.obj (cotangentCochain h) :=
  rfl

/-- The morphism of standard-resolution terms induced by a morphism of algebras over a fixed
base. -/
def standardTermMap {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B C : Under A}
    (h : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    standardTerm A B n ⟶ standardTerm A C n :=
  (Endofunctor.iterate (freeForgetEndo A) (n.unop.len + 1)).map h

/-- Augmentation compatibility for `standardTermMap`. -/
theorem standardTermMap_comp_augmentation {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B C : Under A}
    (h : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    (standardTermMap h n).right ≫ standardAugmentation A C n =
      standardAugmentation A B n ≫ h.right :=
  sorry

/-- Forgetting commutativity of the augmentation compatibility of `standardTermMap`. -/
theorem standardTermMap_comp_augmentation_ring {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B C : Under A}
    (h : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    ringOfMap (standardAugmentation A B n ≫ h.right) =
      ringOfMap (standardTermMap h n).right ≫ ringOfMap (standardAugmentation A C n) :=
  sorry

/-- The square of structure maps used by the first transitivity map in a fixed degree. -/
theorem tensorTerm_w {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B C : Under A}
    (h : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    (standardTerm A B n).hom ≫ (standardTermMap h n).right =
      (standardTerm A C n).hom :=
  (standardTermMap h n).w

/-- Extension along a composite is naturally isomorphic to successive scalar extension. -/
def extendAlongCompIso {X : AlgebraicSpace S}
    {O₀ O₁ O₂ : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    (α : O₀ ⟶ O₁) (β : O₁ ⟶ O₂) :
    extendAlong (α ≫ β) ≅ extendAlong α ⋙ extendAlong β :=
  (Adjunction.leftAdjointCompIso (extendRestrictAdj α) (extendRestrictAdj β)
    (extendRestrictAdj (α ≫ β))
    (SheafOfModules.Restriction.compIso' (ringOfMap α) (ringOfMap β)
      (ringOfMap (α ≫ β))
      ((sheafCompose (smallEtaleTopology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map_comp α β))).symm

/-- The iterated ring-sheaf map of standard-resolution terms induced by a map of bases and
resolved algebras. -/
def iterateRightHom {X : AlgebraicSpace S}
    {A A' : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (n : ℕ) :
    ((Endofunctor.iterate (freeForgetEndo A) n).obj B).right ⟶
      ((Endofunctor.iterate (freeForgetEndo A') n).obj B').right :=
  match n with
  | 0 => β
  | n + 1 =>
      coprod.map α
        ((Sheaf.composeAndSheafify (smallEtaleTopology X) CommRingCat.free).map
          ((sheafCompose (smallEtaleTopology X)
              (CategoryTheory.forget CommRingCat.{u + 1})).map
            (iterateRightHom α β n)))

/-- The ring-sheaf map of standard-resolution terms induced by a map of bases and resolved
algebras. -/
irreducible_def standardTermRightHom {X : AlgebraicSpace S}
    {A A' : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (n : SimplexCategoryᵒᵖ) :
    (standardTerm A B n).right ⟶ (standardTerm A' B' n).right :=
  iterateRightHom α β (n.unop.len + 1)

/-- Structure maps of standard-resolution terms form a commutative square with the induced
termwise ring-sheaf maps. -/
theorem standardTermRightHom_square {X : AlgebraicSpace S}
    {A A' : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    α ≫ (standardTerm A' B' n).hom =
      (standardTerm A B n).hom ≫ standardTermRightHom α β n :=
  sorry

/-- Augmentations of standard-resolution terms form a commutative square with the induced
termwise ring-sheaf maps. -/
theorem standardTermRightHom_comp_augmentation {X : AlgebraicSpace S}
    {A A' : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    ringOfMap (standardAugmentation A B n ≫ β) =
      ringOfMap (standardTermRightHom α β n) ≫
        ringOfMap (standardAugmentation A' B' n) :=
  sorry

/-- Degreewise first transitivity map of simplicial cotangent modules over a fixed base. -/
def tensorSimplicialMap {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B C : Under A}
    (h : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    (extendAlong h.right).obj ((simplicialModule A B).obj n) ⟶ (simplicialModule A C).obj n :=
  (extendAlongCompIso (standardAugmentation A B n) h.right).inv.app
      (differentialsOn (standardTerm A B n).hom) ≫
    ((extendRestrictAdj (standardAugmentation A B n ≫ h.right)).homEquiv _ _).symm
      (@RelativeDifferentials.map.{u + 1, u, u + 1} (smallEtaleSite X) _
        (smallEtaleTopology X) _
        (CategoryTheory.hasWeakSheafify_addCommGrp (smallEtaleTopology X)) _ _ _ _ _ _ _ _ _
        ⟨(Category.id_comp (standardTerm A C n).hom).trans (tensorTerm_w h n).symm⟩ ≫
        (restrictAlong (standardTermMap h n).right).map
          ((extendRestrictAdj (standardAugmentation A C n)).unit.app _) ≫
        (SheafOfModules.Restriction.compIso'
            (ringOfMap (standardTermMap h n).right)
            (ringOfMap (standardAugmentation A C n))
            (ringOfMap (standardAugmentation A B n ≫ h.right))
            (standardTermMap_comp_augmentation_ring h n)).hom.app _)

/-- Underived extension of scalars of `cotangentCochainObj α` along `β`. -/
def pullbackCotangentCochain {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    CochainComplex (CommModules W) ℤ :=
  ((extendAlong (structureMapLift p)).mapHomologicalComplex (up ℤ)).obj
    (cotangentCochainObj (pulledMap p f))

/-- Unfolding of `pullbackCotangentCochain` as extension of scalars of the pulled cotangent. -/
theorem pullbackCotangentCochain_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    pullbackCotangentCochain p f =
      ((extendAlong (structureMapLift p)).mapHomologicalComplex (up ℤ)).obj
        (cotangentCochainObj (pulledMap p f)) :=
  rfl

/-- `Lp^* L_{X/B}` as an object of `D(𝒪_W)`. -/
def pullbackCotangent {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    DerivedCategory (CommModules W) :=
  DerivedCategory.Q.obj (pullbackCotangentCochain p f)

/-- Unfolding of `pullbackCotangent` as `DerivedCategory.Q` of `pullbackCotangentCochain`. -/
theorem pullbackCotangent_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    pullbackCotangent p f = DerivedCategory.Q.obj (pullbackCotangentCochain p f) :=
  rfl

/-- The composite algebra map `p⁻¹(f♯) ≫ p♯` on `W`. -/
abbrev compositeStructureMap {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    pulledInverseImage p f ⟶ commStructureSheafLift W :=
  pulledMap p f ≫ structureMapLift p

/-- The morphism `Under.mk (pulledMap p f) ⟶ Under.mk (compositeStructureMap p f)` induced by
`p♯`. -/
def pulledToComposite {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    Under.mk (pulledMap p f) ⟶ Under.mk (compositeStructureMap p f) :=
  Under.homMk (structureMapLift p) rfl

/-- The unextended first transitivity map
`p^*(L_{X/B}) ⟶ L(p⁻¹(f♯) ≫ p♯)`. -/
private def transitivityMapCochainComponent {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (i : ℤ) : (pullbackCotangentCochain p f).X i ⟶ (cotangentCochainObj (compositeStructureMap p f)).X i :=
    match h : embeddingDownNat.r i with
    | some n =>
        (extendAlong (structureMapLift p)).map
            (extendXIso
              ((alternatingFaceMapComplex
                  (SheafOfModules.{u + 1} (ringOf (inverseImageLift p)))).obj
                (simplicialModule (pulledInverseImage p f) (Under.mk (pulledMap p f))))
              embeddingDownNat
              (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).hom ≫
          tensorSimplicialMap (pulledToComposite p f) (op ⦋n⦌) ≫
          (extendXIso
              ((alternatingFaceMapComplex
                  (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift W)))).obj
                (simplicialModule (pulledInverseImage p f)
                  (Under.mk (compositeStructureMap p f))))
              embeddingDownNat
              (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).inv
    | none => 0

/-- The degreewise cotangent map commutes with the cochain differentials. -/
private theorem transitivityMapCochain_comm {W X B : AlgebraicSpace S}
    (p : W ⟶ X) (f : X ⟶ B) (i j : ℤ) :
    transitivityMapCochainComponent p f i ≫ (cotangentCochainObj (compositeStructureMap p f)).d i j =
      (pullbackCotangentCochain p f).d i j ≫ transitivityMapCochainComponent p f j :=
  sorry

/-- The canonical cochain map between the standard cotangent models. -/
def transitivityMapCochain {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    pullbackCotangentCochain p f ⟶ cotangentCochainObj (compositeStructureMap p f) where
  f := transitivityMapCochainComponent p f
  comm' := fun i j _ ↦ transitivityMapCochain_comm p f i j

/-- The canonical comparison between iterated and composite inverse-image base sheaves. -/
def compositeBaseIso {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    pulledInverseImage p f ≅ inverseImageLift (p ≫ f) :=
  let e := SquareZeroExtension.commSheafInverseImageCompIso p f (commStructureSheaf B)
  { hom := liftSheafMap W e.hom
    inv := liftSheafMap W e.inv
    hom_inv_id :=
      ((liftSheafMap_comp W e.hom e.inv).symm.trans
        (congrArg (fun α ↦ liftSheafMap W α) e.hom_inv_id)).trans (liftSheafMap_id W _)
    inv_hom_id :=
      ((liftSheafMap_comp W e.inv e.hom).symm.trans
        (congrArg (fun α ↦ liftSheafMap W α) e.inv_hom_id)).trans (liftSheafMap_id W _) }

/-- The inverse-image composition comparison respects the geometric structure morphisms. -/
theorem compositeBaseIso_w {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    (compositeBaseIso p f).hom ≫ structureMapLift (p ≫ f) = compositeStructureMap p f :=
  sorry

/-- A change of base sheaf induces a map of the augmented differential modules. -/
private def baseTransportTerm {X : AlgebraicSpace S}
    {A A' O : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    (α : A ⟶ A') (φ : A ⟶ O) (φ' : A' ⟶ O)
    (hα : α ≫ φ' = φ ≫ 𝟙 O) (n : SimplexCategoryᵒᵖ) :
    (simplicialModule A (Under.mk φ)).obj n ⟶
      (simplicialModule A' (Under.mk φ')).obj n :=
  ((extendRestrictAdj (standardAugmentation A (Under.mk φ) n)).homEquiv _ _).symm
    (@RelativeDifferentials.map.{u + 1, u, u + 1} (smallEtaleSite X) _
        (smallEtaleTopology X) _
        (CategoryTheory.hasWeakSheafify_addCommGrp (smallEtaleTopology X)) _ _ _ _ _ _ _ _ _
        ⟨standardTermRightHom_square (B := Under.mk φ) (B' := Under.mk φ')
          α (𝟙 O) hα n⟩ ≫
      (restrictAlong (standardTermRightHom (B := Under.mk φ) (B' := Under.mk φ')
          α (𝟙 O) n)).map
        ((extendRestrictAdj (standardAugmentation A' (Under.mk φ') n)).unit.app _) ≫
      (SheafOfModules.Restriction.compIso'
          (ringOfMap (standardTermRightHom (B := Under.mk φ) (B' := Under.mk φ')
            α (𝟙 O) n))
          (ringOfMap (standardAugmentation A' (Under.mk φ') n))
          (ringOfMap (standardAugmentation A (Under.mk φ) n ≫ 𝟙 O))
          (standardTermRightHom_comp_augmentation (B := Under.mk φ) (B' := Under.mk φ')
            α (𝟙 O) hα n)).hom.app _)

/-- The degreewise map of standard cotangent models induced by a base-sheaf map. -/
private def baseTransportComponent {X : AlgebraicSpace S}
    {A A' O : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    (α : A ⟶ A') (φ : A ⟶ O) (φ' : A' ⟶ O)
    (hα : α ≫ φ' = φ ≫ 𝟙 O) (i : ℤ) :
    (cotangentCochainObj φ).X i ⟶ (cotangentCochainObj φ').X i :=
  match h : embeddingDownNat.r i with
  | some n =>
      (extendXIso ((alternatingFaceMapComplex
        (SheafOfModules.{u + 1} (ringOf O))).obj (simplicialModule A (Under.mk φ)))
        embeddingDownNat (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).hom ≫
      baseTransportTerm α φ φ' hα (op ⦋n⦌) ≫
      (extendXIso ((alternatingFaceMapComplex
        (SheafOfModules.{u + 1} (ringOf O))).obj (simplicialModule A' (Under.mk φ')))
        embeddingDownNat (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).inv
  | none => 0

set_option maxHeartbeats 1200000 in
/-- The forward degreewise cotangent transport along inverse-image composition. -/
private def compositeToBaseHomComponent {W X B : AlgebraicSpace S}
    (p : W ⟶ X) (f : X ⟶ B) (i : ℤ) :
    (cotangentCochainObj (compositeStructureMap p f)).X i ⟶
      (cotangentCochain (p ≫ f)).X i :=
  baseTransportComponent (compositeBaseIso p f).hom
    (compositeStructureMap p f) (structureMapLift (p ≫ f))
    ((compositeBaseIso_w p f).trans (Category.comp_id _).symm) i

set_option maxHeartbeats 1200000 in
/-- The reverse degreewise cotangent transport along inverse-image composition. -/
private def compositeToBaseInvComponent {W X B : AlgebraicSpace S}
    (p : W ⟶ X) (f : X ⟶ B) (i : ℤ) :
    (cotangentCochain (p ≫ f)).X i ⟶
      (cotangentCochainObj (compositeStructureMap p f)).X i :=
  baseTransportComponent (compositeBaseIso p f).inv
    (structureMapLift (p ≫ f)) (compositeStructureMap p f)
    (((congrArg (fun α ↦ (compositeBaseIso p f).inv ≫ α)
      (compositeBaseIso_w p f).symm).trans
      ((compositeBaseIso p f).inv_hom_id_assoc _)).trans (Category.comp_id _).symm) i

/-- Cotangent transport commutes with differentials and has mutually inverse components. -/
private theorem compositeToBaseIso_laws {W X B : AlgebraicSpace S}
    (p : W ⟶ X) (f : X ⟶ B) :
    (∀ i j, compositeToBaseHomComponent p f i ≫ (cotangentCochain (p ≫ f)).d i j =
      (cotangentCochainObj (compositeStructureMap p f)).d i j ≫
        compositeToBaseHomComponent p f j) ∧
    (∀ i j, compositeToBaseInvComponent p f i ≫
        (cotangentCochainObj (compositeStructureMap p f)).d i j =
      (cotangentCochain (p ≫ f)).d i j ≫ compositeToBaseInvComponent p f j) ∧
    (∀ i, compositeToBaseHomComponent p f i ≫ compositeToBaseInvComponent p f i = 𝟙 _) ∧
    (∀ i, compositeToBaseInvComponent p f i ≫ compositeToBaseHomComponent p f i = 𝟙 _) :=
  sorry

/-- The cotangent models of the iterated and composite inverse-image structure maps
are canonically isomorphic. -/
def compositeToBaseIso {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    cotangentCochainObj (compositeStructureMap p f) ≅ cotangentCochain (p ≫ f) where
  hom := { f := compositeToBaseHomComponent p f
           comm' := fun i j _ ↦ (compositeToBaseIso_laws p f).1 i j }
  inv := { f := compositeToBaseInvComponent p f
           comm' := fun i j _ ↦ (compositeToBaseIso_laws p f).2.1 i j }
  hom_inv_id := HomologicalComplex.hom_ext _ _ (compositeToBaseIso_laws p f).2.2.1
  inv_hom_id := HomologicalComplex.hom_ext _ _ (compositeToBaseIso_laws p f).2.2.2


/-- The first map `Lp^* L_{X/B} ⟶ L_{W/B}` of the transitivity triangle in `D(𝒪_W)`. -/
def transitivityMap {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    pullbackCotangent p f ⟶ cotangent (p ≫ f) :=
  DerivedCategory.Q.map (transitivityMapCochain p f ≫ (compositeToBaseIso p f).hom)

/-- Unfolding of `transitivityMap` as `Q.map` of `transitivityMapCochain` composed with
`compositeToBaseIso`. -/
theorem transitivityMap_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    transitivityMap p f =
      DerivedCategory.Q.map (transitivityMapCochain p f ≫ (compositeToBaseIso p f).hom) :=
  rfl

/-- The commutative square of structure maps used by the second transitivity map. -/
theorem toRelativeSquare {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    CommSq (pulledMap p f) (compositeStructureMap p f) (structureMapLift p) (𝟙 _) :=
  ⟨rfl⟩

/-- The commutative square of standard-resolution terms used by the second transitivity map. -/
theorem relativeTermSquare {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) :
    CommSq (pulledMap p f)
      (standardTerm (pulledInverseImage p f) (Under.mk (compositeStructureMap p f)) n).hom
      (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).hom
      (standardTermRightHom
          (B := Under.mk (compositeStructureMap p f))
          (B' := Under.mk (structureMapLift p)) (pulledMap p f) (𝟙 (commStructureSheafLift W)) n) :=
  sorry

/-- Termwise base-change of relative differentials along `relativeTermSquare`. -/
def relativeDifferentialsTermMap {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) :
    differentialsOn
        (standardTerm (pulledInverseImage p f) (Under.mk (compositeStructureMap p f)) n).hom ⟶
      (restrictAlong (standardTermRightHom
          (B := Under.mk (compositeStructureMap p f))
          (B' := Under.mk (structureMapLift p)) (pulledMap p f)
          (𝟙 (commStructureSheafLift W)) n)).obj
        (differentialsOn
          (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).hom) :=
  @RelativeDifferentials.map.{u + 1, u, u + 1} (smallEtaleSite W) _
      (smallEtaleTopology W) _
      (CategoryTheory.hasWeakSheafify_addCommGrp (smallEtaleTopology W)) _ _ _ _ _ _ _ _ _
    (relativeTermSquare p f n)

/-- Ring-level augmentation compatibility for `relativeTermSquare`. -/
theorem relativeAugmentation_comp_ring {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) :
    ringOfMap (standardAugmentation (pulledInverseImage p f)
        (Under.mk (compositeStructureMap p f)) n) =
      ringOfMap (standardTermRightHom
          (B := Under.mk (compositeStructureMap p f))
          (B' := Under.mk (structureMapLift p)) (pulledMap p f) (𝟙 (commStructureSheafLift W)) n) ≫
        ringOfMap (standardAugmentation (inverseImageLift p)
          (Under.mk (structureMapLift p)) n) :=
  sorry

set_option maxHeartbeats 1200000 in
/-- Degreewise second transitivity map of simplicial cotangent modules, changing the base
ring sheaf while keeping the total algebra `𝒪_W`. -/
def relativeSimplicialMap {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) :
    (simplicialModule (pulledInverseImage p f)
        (Under.mk (compositeStructureMap p f))).obj n ⟶
      (simplicialModule (inverseImageLift p) (Under.mk (structureMapLift p))).obj n :=
  ((extendRestrictAdj
        (standardAugmentation (pulledInverseImage p f)
          (Under.mk (compositeStructureMap p f)) n)).homEquiv _ _).symm
    (relativeDifferentialsTermMap p f n ≫
      (restrictAlong (standardTermRightHom
          (B := Under.mk (compositeStructureMap p f))
          (B' := Under.mk (structureMapLift p)) (pulledMap p f)
          (𝟙 (commStructureSheafLift W)) n)).map
        ((extendRestrictAdj (standardAugmentation (inverseImageLift p)
          (Under.mk (structureMapLift p)) n)).unit.app _) ≫
      (SheafOfModules.Restriction.compIso'
        (ringOfMap (standardTermRightHom
          (B := Under.mk (compositeStructureMap p f))
          (B' := Under.mk (structureMapLift p)) (pulledMap p f)
          (𝟙 (commStructureSheafLift W)) n))
        (ringOfMap (standardAugmentation (inverseImageLift p)
          (Under.mk (structureMapLift p)) n))
        (ringOfMap (standardAugmentation (pulledInverseImage p f)
          (Under.mk (compositeStructureMap p f)) n))
        (relativeAugmentation_comp_ring p f n)).hom.app _)

/-- The unextended second transitivity map `L_{W/B} ⟶ L_{W/X}`, induced by base change of
relative differentials along `p♯`. -/
private def toRelativeMapCochainComponent {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (i : ℤ) : (cotangentCochainObj (compositeStructureMap p f)).X i ⟶ (cotangentCochain p).X i :=
    match h : embeddingDownNat.r i with
    | some n =>
        (extendXIso
            ((alternatingFaceMapComplex
                (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift W)))).obj
              (simplicialModule (pulledInverseImage p f)
                (Under.mk (compositeStructureMap p f))))
            embeddingDownNat
            (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).hom ≫
          relativeSimplicialMap p f (op ⦋n⦌) ≫
          (extendXIso
              ((alternatingFaceMapComplex
                  (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift W)))).obj
                (simplicialModule (inverseImageLift p) (Under.mk (structureMapLift p))))
              embeddingDownNat
              (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).inv
    | none => 0

/-- The degreewise cotangent map commutes with the cochain differentials. -/
private theorem toRelativeMapCochain_comm {W X B : AlgebraicSpace S}
    (p : W ⟶ X) (f : X ⟶ B) (i j : ℤ) :
    toRelativeMapCochainComponent p f i ≫ (cotangentCochain p).d i j =
      (cotangentCochainObj (compositeStructureMap p f)).d i j ≫ toRelativeMapCochainComponent p f j :=
  sorry

/-- The canonical cochain map between the standard cotangent models. -/
def toRelativeMapCochain {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    cotangentCochainObj (compositeStructureMap p f) ⟶ cotangentCochain p where
  f := toRelativeMapCochainComponent p f
  comm' := fun i j _ ↦ toRelativeMapCochain_comm p f i j

/-- The second map `L_{W/B} ⟶ L_{W/X}` of the transitivity triangle in `D(𝒪_W)`. -/
def toRelativeMap {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    cotangent (p ≫ f) ⟶ cotangent p :=
  DerivedCategory.Q.map ((compositeToBaseIso p f).inv ≫ toRelativeMapCochain p f)

/-- Unfolding of `toRelativeMap` as `Q.map` of `compositeToBaseIso.inv` composed with
`toRelativeMapCochain`. -/
theorem toRelativeMap_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    toRelativeMap p f =
      DerivedCategory.Q.map ((compositeToBaseIso p f).inv ≫ toRelativeMapCochain p f) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Cotangent
