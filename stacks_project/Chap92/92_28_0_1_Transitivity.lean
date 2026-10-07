module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.MvPolynomial.Derivation
public import Mathlib.Algebra.TrivSqZeroExt.Basic
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
public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Generators
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Natural
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_28_1_Hom
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf
public import stacks_project.Chap69.Definition_69_6_2_ExtensionByZero
public import stacks_project.Chap92.Definition_92_22_1_Cotangent

/-!
# Transitivity of cotangent complexes of algebraic spaces

For composable morphisms `W ⟶ X ⟶ B` of algebraic spaces over a scheme `S`, this module
owns the cochain and derived cotangent complexes `L_{X/B}`, `Lp^* L_{X/B}`, and `L_{W/X}`,
together with the three maps of the transitivity triangle in `D(O_W)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Sheaf
open CategoryTheory.Sheaf.InternalCommRing
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
open TrivSqZeroExt
open CategoryTheory.Sheaf.FreeAlgebra

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
    (SheafOfModules.restrictScalars.{u + 1} α).IsRightAdjoint :=
  sorry

/-- Binary coproducts of lifted commutative ring sheaves on the small étale site. -/
instance (priority := high) sheafCommRing_succ_hasBinaryCoproducts (X : AlgebraicSpace S) :
    HasColimitsOfShape (Discrete WalkingPair)
      (Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}) :=
  sorry

/-- Sheaf composition along `forget₂ CommRingCat RingCat` on the small étale site. -/
instance hasSheafCompose_forget₂_commRing_succ (X : AlgebraicSpace S) :
    (smallEtaleTopology X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  sorry

/-- Weak sheafification of lifted commutative ring sheaves on the small étale site. -/
instance hasWeakSheafify_commRing_succ (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) CommRingCat.{u + 1} :=
  sorry

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

/-- Inverse image of a commutative-ring sheaf along a morphism of algebraic spaces. -/
def commSheafInverseImageObj {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  fromInternalObj.{u + 1, u, u}
    ((internalCommRingInverseImage h).obj (toInternalObj.{u + 1, u, u} R))

/-- Inverse image of a morphism of commutative-ring sheaves along a morphism of algebraic
spaces. -/
def commSheafInverseImageMap {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    {R R' : Sheaf (smallEtaleTopology Y) CommRingCat.{u}} (α : R ⟶ R') :
    commSheafInverseImageObj h R ⟶ commSheafInverseImageObj h R' :=
  fromInternalMap.{u + 1, u, u}
    ((internalCommRingInverseImage h).map (toInternalMap.{u + 1, u, u} α))

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
  relativeDifferentials.{u + 1, u, u + 1} (C := smallEtaleSite X) (J := smallEtaleTopology X) φ

/-- Restriction of lifted module sheaves along a morphism of lifted ring sheaves. -/
abbrev restrictAlong {X : AlgebraicSpace S}
    {O₀ O₁ : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (α : O₀ ⟶ O₁) :
    SheafOfModules.{u + 1} (ringOf O₁) ⥤ SheafOfModules.{u + 1} (ringOf O₀) :=
  SheafOfModules.restrictScalars (ringOfMap α)

/-- Underlying carrier of a section after restriction of scalars. This is the identity on
the underlying abelian group, and avoids unifying distinct `restrictAlong` module sheaves. -/
def restrictAlongCarrier {X : AlgebraicSpace S}
    {O₀ O₁ : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (α : O₀ ⟶ O₁)
    {M : SheafOfModules.{u + 1} (ringOf O₁)} {U : (smallEtaleSite X)ᵒᵖ}
    (x : ((restrictAlong α).obj M).val.obj U) : M.val.obj U :=
  x

/-- Inverse of `restrictAlongCarrier` on underlying carriers. -/
def restrictAlongCarrierSymm {X : AlgebraicSpace S}
    {O₀ O₁ : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} (α : O₀ ⟶ O₁)
    {M : SheafOfModules.{u + 1} (ringOf O₁)} {U : (smallEtaleSite X)ᵒᵖ}
    (x : M.val.obj U) : ((restrictAlong α).obj M).val.obj U :=
  x

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
  RelativeDifferentials.map.{u + 1, u, u + 1} (C := smallEtaleSite X) (J := smallEtaleTopology X)
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
  sorry

/-- The cotangent complex `L_{X/Y}` of a morphism of algebraic spaces, as an object of
`D(𝒪_X)`. -/
def cotangent {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    DerivedCategory (CommModules X) :=
  DerivedCategory.Q.obj (cotangentCochain h)

/-- Unfolding of `cotangent` as `DerivedCategory.Q` of `cotangentCochain`. -/
theorem cotangent_eq {X Y : AlgebraicSpace S} (h : X ⟶ Y) :
    cotangent h = DerivedCategory.Q.obj (cotangentCochain h) :=
  sorry

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
  sorry

/-- Successive extensions of scalars along composable lifted ring-sheaf morphisms. -/
theorem extendAlong_comp_obj {X : AlgebraicSpace S}
    {O₀ O₁ O₂ : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}}
    (α : O₀ ⟶ O₁) (β : O₁ ⟶ O₂) (M : SheafOfModules.{u + 1} (ringOf O₀)) :
    (extendAlong β).obj ((extendAlong α).obj M) = (extendAlong (α ≫ β)).obj M :=
  sorry

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
  eqToHom
      (extendAlong_comp_obj (standardAugmentation A B n) h.right
        (differentialsOn (standardTerm A B n).hom)) ≫
    ((extendRestrictAdj (standardAugmentation A B n ≫ h.right)).homEquiv _ _).symm
      (RelativeDifferentials.map.{u + 1, u, u + 1} (C := smallEtaleSite X) (J := smallEtaleTopology X)
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
  sorry

/-- `Lp^* L_{X/B}` as an object of `D(𝒪_W)`. -/
def pullbackCotangent {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    DerivedCategory (CommModules W) :=
  DerivedCategory.Q.obj (pullbackCotangentCochain p f)

/-- Unfolding of `pullbackCotangent` as `DerivedCategory.Q` of `pullbackCotangentCochain`. -/
theorem pullbackCotangent_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    pullbackCotangent p f = DerivedCategory.Q.obj (pullbackCotangentCochain p f) :=
  sorry

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
def transitivityMapCochain {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    pullbackCotangentCochain p f ⟶ cotangentCochainObj (compositeStructureMap p f) where
  f i :=
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
  comm' := sorry

/-- Identification of the composite cotangent `L(p⁻¹(f♯) ≫ p♯)` with `L_{W/B}`. -/
theorem compositeToBase_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    cotangentCochainObj (compositeStructureMap p f) = cotangentCochain (p ≫ f) :=
  sorry

/-- Cochain-level identification of `L(p⁻¹(f♯) ≫ p♯)` with `L_{W/B}`. -/
def compositeToBaseIso {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    cotangentCochainObj (compositeStructureMap p f) ≅ cotangentCochain (p ≫ f) :=
  eqToIso (compositeToBase_eq p f)

/-- Unfolding of `compositeToBaseIso` as `eqToIso` of `compositeToBase_eq`. -/
theorem compositeToBaseIso_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    compositeToBaseIso p f = eqToIso (compositeToBase_eq p f) :=
  sorry

/-- The first map `Lp^* L_{X/B} ⟶ L_{W/B}` of the transitivity triangle in `D(𝒪_W)`. -/
def transitivityMap {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    pullbackCotangent p f ⟶ cotangent (p ≫ f) :=
  DerivedCategory.Q.map (transitivityMapCochain p f ≫ (compositeToBaseIso p f).hom)

/-- Unfolding of `transitivityMap` as `Q.map` of `transitivityMapCochain` composed with
`compositeToBaseIso`. -/
theorem transitivityMap_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    transitivityMap p f =
      DerivedCategory.Q.map (transitivityMapCochain p f ≫ (compositeToBaseIso p f).hom) :=
  sorry

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
      (standardTermRightHom (pulledMap p f) (𝟙 (commStructureSheafLift W)) n) :=
  sorry

/-- Termwise base-change of relative differentials along `relativeTermSquare`. -/
def relativeDifferentialsTermMap {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) :
    differentialsOn
        (standardTerm (pulledInverseImage p f) (Under.mk (compositeStructureMap p f)) n).hom ⟶
      (restrictAlong (standardTermRightHom (pulledMap p f)
          (𝟙 (commStructureSheafLift W)) n)).obj
        (differentialsOn
          (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).hom) :=
  RelativeDifferentials.map.{u + 1, u, u + 1} (C := smallEtaleSite W) (J := smallEtaleTopology W)
    (relativeTermSquare p f n)

/-- Ring-level augmentation compatibility for `relativeTermSquare`. -/
theorem relativeAugmentation_comp_ring {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) :
    ringOfMap (standardAugmentation (pulledInverseImage p f)
        (Under.mk (compositeStructureMap p f)) n) =
      ringOfMap (standardTermRightHom (pulledMap p f) (𝟙 (commStructureSheafLift W)) n) ≫
        ringOfMap (standardAugmentation (inverseImageLift p)
          (Under.mk (structureMapLift p)) n) :=
  sorry

/-- Restriction of a `W/X` simplicial cotangent term along the degree-`n` standard-term
ring map is the augmentation-restriction of that same term. -/
theorem relativeRestrictedTarget_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) :
    (restrictAlong
        (standardTermRightHom (pulledMap p f) (𝟙 (commStructureSheafLift W)) n)).obj
      (differentialsOn
        (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).hom) =
      (restrictAlong
          (standardAugmentation (pulledInverseImage p f)
            (Under.mk (compositeStructureMap p f)) n)).obj
        ((simplicialModule (inverseImageLift p) (Under.mk (structureMapLift p))).obj n) :=
  sorry

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
      eqToHom (relativeRestrictedTarget_eq p f n))

/-- The unextended second transitivity map `L_{W/B} ⟶ L_{W/X}`, induced by base change of
relative differentials along `p♯`. -/
def toRelativeMapCochain {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    cotangentCochainObj (compositeStructureMap p f) ⟶ cotangentCochain p where
  f i :=
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
  comm' := sorry

/-- The second map `L_{W/B} ⟶ L_{W/X}` of the transitivity triangle in `D(𝒪_W)`. -/
def toRelativeMap {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    cotangent (p ≫ f) ⟶ cotangent p :=
  DerivedCategory.Q.map ((compositeToBaseIso p f).inv ≫ toRelativeMapCochain p f)

/-- Unfolding of `toRelativeMap` as `Q.map` of `compositeToBaseIso.inv` composed with
`toRelativeMapCochain`. -/
theorem toRelativeMap_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    toRelativeMap p f =
      DerivedCategory.Q.map ((compositeToBaseIso p f).inv ≫ toRelativeMapCochain p f) :=
  sorry

/-- Restriction of `Lp^*` of the degree-`n` `X/B` simplicial cotangent term along the
augmentation of the degree-`n+1` `W/X` standard-resolution algebra. -/
abbrev connectingTarget {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) (n : ℕ) :
    SheafOfModules.{u + 1}
      (ringOf (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
        (op ⦋n + 1⦌)).right) :=
  (restrictAlong
      (standardAugmentation (inverseImageLift p) (Under.mk (structureMapLift p))
        (op ⦋n + 1⦌))).obj
    ((extendAlong (structureMapLift p)).obj
      ((simplicialModule (pulledInverseImage p f) (Under.mk (pulledMap p f))).obj
        (op ⦋n⦌)))

/-- Unfolding of `connectingTarget` as restriction of the extended degree-`n` `X/B` term. -/
theorem connectingTarget_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : ℕ) :
    connectingTarget p f n =
      (restrictAlong
          (standardAugmentation (inverseImageLift p) (Under.mk (structureMapLift p))
            (op ⦋n + 1⦌))).obj
        ((extendAlong (structureMapLift p)).obj
          ((simplicialModule (pulledInverseImage p f) (Under.mk (pulledMap p f))).obj
            (op ⦋n⦌))) :=
  sorry

/-- Iterated universal generator of a standard-resolution algebra sheaf. -/
def standardGenerator {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B : Under A} (n : ℕ) :
    (sheafCompose (smallEtaleTopology X)
        (CategoryTheory.forget CommRingCat.{u + 1})).obj B.right ⟶
      (sheafCompose (smallEtaleTopology X)
        (CategoryTheory.forget CommRingCat.{u + 1})).obj
        (standardTerm A B (op ⦋n⦌)).right :=
  CategoryTheory.Adjunction.unit.iterateApp (freeForgetAdjunction A) B n

/-- Unfolding of `standardGenerator` as the iterated unit of `freeForgetAdjunction`. -/
theorem standardGenerator_eq {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u + 1}} {B : Under A} (n : ℕ) :
    standardGenerator (A := A) (B := B) n =
      CategoryTheory.Adjunction.unit.iterateApp (freeForgetAdjunction A) B n :=
  sorry

/-- Underlying sheaf of sets of the degree-`n` `W/X` standard-resolution algebra. -/
abbrev connectingGenerators {W X : AlgebraicSpace S} (p : W ⟶ X) (n : ℕ) :
    Sheaf (smallEtaleTopology W) (Type (u + 1)) :=
  (sheafCompose (smallEtaleTopology W)
      (CategoryTheory.forget CommRingCat.{u + 1})).obj
    (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
      (op ⦋n⦌)).right

/-- Unfolding of `connectingGenerators` as the underlying sheaf of the degree-`n` `W/X`
standard-resolution term. -/
theorem connectingGenerators_eq {W X : AlgebraicSpace S} (p : W ⟶ X) (n : ℕ) :
    connectingGenerators p n =
      (sheafCompose (smallEtaleTopology W)
          (CategoryTheory.forget CommRingCat.{u + 1})).obj
        (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
          (op ⦋n⦌)).right :=
  sorry

/-- The free-forgetful unit including the generating sheaf of the previous iterate into the
degree-`n+1` `W/X` standard-resolution algebra. -/
def connectingGeneratorInclude {W X : AlgebraicSpace S} (p : W ⟶ X) (n : ℕ) :
    connectingGenerators p n ⟶
      (sheafCompose (smallEtaleTopology W)
          (CategoryTheory.forget CommRingCat.{u + 1})).obj
        (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
          (op ⦋n + 1⦌)).right :=
  (freeForgetAdjunction (inverseImageLift p)).unit.app (connectingGenerators p n)

/-- Unfolding of `connectingGeneratorInclude` as the unit of `freeForgetAdjunction` at the
previous iterate. -/
theorem connectingGeneratorInclude_eq {W X : AlgebraicSpace S} (p : W ⟶ X) (n : ℕ) :
    connectingGeneratorInclude p n =
      (freeForgetAdjunction (inverseImageLift p)).unit.app (connectingGenerators p n) :=
  sorry

/-- The two transitivity cochain maps compose to zero. -/
theorem transitivityMapCochain_comp_toRelative {W X B : AlgebraicSpace S}
    (p : W ⟶ X) (f : X ⟶ B) :
    transitivityMapCochain p f ≫ toRelativeMapCochain p f = 0 :=
  sorry

/-- The termwise 08UP short complex `Lp^* L_{X/B} ⟶ L_{W/B} ⟶ L_{W/X}` of cochain
complexes of `𝒪_W`-modules. -/
def transitivityShortComplex {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    ShortComplex (CochainComplex (CommModules W) ℤ) :=
  ShortComplex.mk (transitivityMapCochain p f) (toRelativeMapCochain p f)
    (transitivityMapCochain_comp_toRelative p f)

/-- Augmentation of a `W/X` standard-resolution section to `𝒪_W`. -/
def transitivitySectionAugment {W X : AlgebraicSpace S} (p : W ⟶ X)
    (n : SimplexCategoryᵒᵖ) {U : (smallEtaleSite W)ᵒᵖ}
    (r : (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).right.obj.obj U) :
    (commStructureSheafLift W).obj.obj U :=
  ConcreteCategory.hom
    ((standardAugmentation (inverseImageLift p) (Under.mk (structureMapLift p)) n).hom.app U) r

/-- Iterated free generator in `Q_n` of the augmentation of a `W/X` section. -/
def transitivitySectionGenerator {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) {U : (smallEtaleSite W)ᵒᵖ}
    (r : (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).right.obj.obj U) :
    (standardTerm (pulledInverseImage p f) (Under.mk (compositeStructureMap p f)) n).right.obj.obj U :=
  (standardGenerator (A := pulledInverseImage p f)
      (B := Under.mk (compositeStructureMap p f)) n.unop.len).hom.app U
    (transitivitySectionAugment p n r)

/-- Kähler differential of the iterated `Q_n`-generator of the augmentation of a `W/X`
section. -/
def transitivitySectionValue {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) {U : (smallEtaleSite W)ᵒᵖ}
    (r : (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).right.obj.obj U) :
    (differentialsOn
      (standardTerm (pulledInverseImage p f) (Under.mk (compositeStructureMap p f)) n).hom).val.obj U :=
  (relativeDifferential
      (standardTerm (pulledInverseImage p f) (Under.mk (compositeStructureMap p f)) n).hom).d
    (transitivitySectionGenerator p f n r)

/-- Restricted degree-`n` `W/B` simplicial cotangent term, as an `R_n`-module via the
`W/X` augmentation. -/
abbrev transitivitySectionTarget {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) :
    SheafOfModules.{u + 1}
      (ringOf (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).right) :=
  (restrictAlong
      (standardAugmentation (inverseImageLift p) (Under.mk (structureMapLift p)) n)).obj
    ((simplicialModule (pulledInverseImage p f)
        (Under.mk (compositeStructureMap p f))).obj n)

/-- Unfolding of `transitivitySectionTarget` as restriction of the degree-`n` `W/B`
simplicial cotangent term. -/
theorem transitivitySectionTarget_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) :
    transitivitySectionTarget p f n =
      (restrictAlong
          (standardAugmentation (inverseImageLift p) (Under.mk (structureMapLift p)) n)).obj
        ((simplicialModule (pulledInverseImage p f)
            (Under.mk (compositeStructureMap p f))).obj n) :=
  sorry

/-- Sectionwise additive map of `transitivitySectionDerivation`, valued in the unextended
degree-`n` `W/B` Kähler module. -/
def transitivitySectionDerivationAdd {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) (U : (smallEtaleSite W)ᵒᵖ) :
    (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).right.obj.obj U →+
      (differentialsOn
          (standardTerm (pulledInverseImage p f)
            (Under.mk (compositeStructureMap p f)) n).hom).val.obj U :=
  AddMonoidHom.mk' (fun r ↦ transitivitySectionValue p f n r) sorry

/-- Unfolding of `transitivitySectionDerivationAdd` as `transitivitySectionValue`. -/
theorem transitivitySectionDerivationAdd_apply {W X B : AlgebraicSpace S} (p : W ⟶ X)
    (f : X ⟶ B) (n : SimplexCategoryᵒᵖ) {U : (smallEtaleSite W)ᵒᵖ}
    (r : (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).right.obj.obj U) :
    transitivitySectionDerivationAdd p f n U r = transitivitySectionValue p f n r :=
  sorry

/-- Unit of `extendRestrictAdj` along the `W/B` augmentation, used to extend Kähler values
into the restricted simplicial `W/B` term. -/
def transitivitySectionUnit {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) :
    differentialsOn
        (standardTerm (pulledInverseImage p f)
          (Under.mk (compositeStructureMap p f)) n).hom ⟶
      (restrictAlong
          (standardAugmentation (pulledInverseImage p f)
            (Under.mk (compositeStructureMap p f)) n)).obj
        ((simplicialModule (pulledInverseImage p f)
            (Under.mk (compositeStructureMap p f))).obj n) :=
  (extendRestrictAdj
      (standardAugmentation (pulledInverseImage p f)
        (Under.mk (compositeStructureMap p f)) n)).unit.app
    (differentialsOn
      (standardTerm (pulledInverseImage p f)
        (Under.mk (compositeStructureMap p f)) n).hom)

/-- Unfolding of `transitivitySectionUnit` as the adjunction unit at the degree-`n` `W/B`
Kähler module. -/
theorem transitivitySectionUnit_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) :
    transitivitySectionUnit p f n =
      (extendRestrictAdj
          (standardAugmentation (pulledInverseImage p f)
            (Under.mk (compositeStructureMap p f)) n)).unit.app
        (differentialsOn
          (standardTerm (pulledInverseImage p f)
            (Under.mk (compositeStructureMap p f)) n).hom) :=
  sorry

/-- Degreewise derivation of the `W/X` standard-resolution algebra with values in the
restricted degree-`n` `W/B` simplicial cotangent term. On a section `r` it sends `r` to
the image of `d(X_{ε(r)})` under the `W/B` adjunction unit, transported on underlying
carriers from restriction along `aug_WB` to restriction along `aug_WX`. -/
def transitivitySectionDerivation {W X B : AlgebraicSpace S} (p : W ⟶ X)
    (f : X ⟶ B) (n : SimplexCategoryᵒᵖ) :
    (transitivitySectionTarget p f n).val.Derivation'
      (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).hom.hom where
  d {U} := AddMonoidHom.mk'
      (fun r ↦
        restrictAlongCarrierSymm
          (standardAugmentation (inverseImageLift p) (Under.mk (structureMapLift p)) n)
          (restrictAlongCarrier
            (standardAugmentation (pulledInverseImage p f)
              (Under.mk (compositeStructureMap p f)) n)
            ((transitivitySectionUnit p f n).val.app U
              (transitivitySectionValue p f n r))))
      sorry
  d_mul := sorry
  d_map := sorry
  d_app := sorry

/-- Unfolding of `transitivitySectionDerivation` as carrier transport of the `W/B` unit
applied to `transitivitySectionValue`. -/
theorem transitivitySectionDerivation_apply {W X B : AlgebraicSpace S} (p : W ⟶ X)
    (f : X ⟶ B) (n : SimplexCategoryᵒᵖ) {U : (smallEtaleSite W)ᵒᵖ}
    (r : (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).right.obj.obj U) :
    (transitivitySectionDerivation p f n).d r =
      restrictAlongCarrierSymm
        (standardAugmentation (inverseImageLift p) (Under.mk (structureMapLift p)) n)
        (restrictAlongCarrier
          (standardAugmentation (pulledInverseImage p f)
            (Under.mk (compositeStructureMap p f)) n)
          ((transitivitySectionUnit p f n).val.app U
            (transitivitySectionValue p f n r))) :=
  sorry

/-- Degreewise section of `relativeSimplicialMap`, from the universal property of
`Ω_{R_n / p⁻¹ 𝒪_X}`. -/
def transitivitySectionSimplicial {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : SimplexCategoryᵒᵖ) :
    (simplicialModule (inverseImageLift p) (Under.mk (structureMapLift p))).obj n ⟶
      (simplicialModule (pulledInverseImage p f)
          (Under.mk (compositeStructureMap p f))).obj n :=
  ((extendRestrictAdj
        (standardAugmentation (inverseImageLift p) (Under.mk (structureMapLift p)) n)).homEquiv
      _ _).symm
    (relativeDifferentialDesc
      (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) n).hom
      (transitivitySectionDerivation p f n))

/-- Degreewise section of the second transitivity cochain map. -/
def transitivitySection {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) (i : ℤ) :
    (cotangentCochain p).X i ⟶ (cotangentCochainObj (compositeStructureMap p f)).X i :=
  match h : embeddingDownNat.r i with
  | some n =>
      (extendXIso
          ((alternatingFaceMapComplex
              (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift W)))).obj
            (simplicialModule (inverseImageLift p) (Under.mk (structureMapLift p))))
          embeddingDownNat
          (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).hom ≫
        transitivitySectionSimplicial p f (op ⦋n⦌) ≫
        (extendXIso
            ((alternatingFaceMapComplex
                (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift W)))).obj
              (simplicialModule (pulledInverseImage p f)
                (Under.mk (compositeStructureMap p f))))
            embeddingDownNat
            (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).inv
  | none => 0

/-- The degreewise section composes to the identity on `L_{W/X}`. -/
theorem transitivitySection_comp {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (k : ℤ) :
    transitivitySection p f k ≫ (toRelativeMapCochain p f).f k = 𝟙 _ :=
  sorry

/-- Exactness of the degree-`k` 08UP short complex of `𝒪_W`-modules. -/
theorem transitivity_eval_exact {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (k : ℤ) :
    ((transitivityShortComplex p f).map
        (HomologicalComplex.eval (CommModules W) (up ℤ) k)).Exact :=
  sorry

/-- The first transitivity map is a monomorphism in each cohomological degree. -/
theorem transitivity_eval_mono {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (k : ℤ) :
    Mono (((transitivityShortComplex p f).map
        (HomologicalComplex.eval (CommModules W) (up ℤ) k)).f) :=
  sorry

/-- Degreewise splitting of the 08UP short complex, from the canonical section of the
second map. -/
def transitivitySplitting {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) (k : ℤ) :
    ((transitivityShortComplex p f).map
        (HomologicalComplex.eval (CommModules W) (up ℤ) k)).Splitting :=
  ShortComplex.Splitting.ofExactOfSection _
    (transitivity_eval_exact p f k)
    (transitivitySection p f k)
    (transitivitySection_comp p f k)
    (transitivity_eval_mono p f k)

/-- The cochain-level 08UP connecting map `L_{W/X} ⟶ (Lp^* L_{X/B})⟦1⟧`. -/
def transitivityConnectingCochain {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    cotangentCochain p ⟶ (pullbackCotangentCochain p f)⟦(1 : ℤ)⟧ :=
  CochainComplex.homOfDegreewiseSplit (transitivityShortComplex p f)
    (transitivitySplitting p f)

/-- Shift identification used by the 08UP connecting cochain on degree `-(n+1)`. -/
theorem transitivityConnecting_shiftEq (n : ℕ) :
    (-n : ℤ) = -(n + 1 : ℤ) + 1 :=
  sorry

/-- The component of the termwise-split 08UP connecting map on a free generator of the
degree-`n+1` `W/X` standard-resolution algebra. The generator is a section of the previous
iterate; its value is the image of `d(X_g)` under the connecting cochain of the termwise-split
simplicial short exact sequence
`0 → Ω_{P_•/A} ⊗ 𝒪_W → Ω_{Q_•/A} ⊗ 𝒪_W → Ω_{R_•/B} ⊗ 𝒪_W → 0`. -/
def connectingGeneratorValue {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : ℕ) {U : (smallEtaleSite W)ᵒᵖ}
    (g : (connectingGenerators p n).obj.obj U) :
    (connectingTarget p f n).val.obj U :=
  let dxg :=
    (relativeDifferential
        (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
          (op ⦋n + 1⦌)).hom).d
      ((connectingGeneratorInclude p n).hom.app U g)
  let ext :=
    ((extendRestrictAdj
          (standardAugmentation (inverseImageLift p) (Under.mk (structureMapLift p))
            (op ⦋n + 1⦌))).unit.app
        (differentialsOn
          (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
            (op ⦋n + 1⦌)).hom)).val.app U dxg
  let inCochain :=
    ConcreteCategory.hom ((cotangentXIso (structureMapLift p) (n + 1)).inv.val.app U)
      (ext :
        ((simplicialModule (inverseImageLift p) (Under.mk (structureMapLift p))).obj
          (op ⦋n + 1⦌)).val.obj U)
  let img :=
    ConcreteCategory.hom
      (((transitivityConnectingCochain p f).f (-(n + 1 : ℤ))).val.app U) inCochain
  let unshifted :=
    ConcreteCategory.hom
      ((CochainComplex.shiftFunctorObjXIso (pullbackCotangentCochain p f) (1 : ℤ)
          (-(n + 1 : ℤ)) (-n : ℤ) (transitivityConnecting_shiftEq n)).hom.val.app U) img
  (ConcreteCategory.hom
    (((extendAlong (structureMapLift p)).map
        (cotangentXIso (pulledMap p f) n).hom).val.app U) unshifted :
    (connectingTarget p f n).val.obj U)

/-- Unfolding of `connectingGeneratorValue` as the 08UP connecting cochain applied to the
Kähler differential of the free generator `X_g`. -/
theorem connectingGeneratorValue_eq {W X B : AlgebraicSpace S} (p : W ⟶ X)
    (f : X ⟶ B) (n : ℕ) {U : (smallEtaleSite W)ᵒᵖ}
    (g : (connectingGenerators p n).obj.obj U) :
    connectingGeneratorValue p f n g =
      let dxg :=
        (relativeDifferential
            (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
              (op ⦋n + 1⦌)).hom).d
          ((connectingGeneratorInclude p n).hom.app U g)
      let ext :=
        ((extendRestrictAdj
              (standardAugmentation (inverseImageLift p) (Under.mk (structureMapLift p))
                (op ⦋n + 1⦌))).unit.app
            (differentialsOn
              (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
                (op ⦋n + 1⦌)).hom)).val.app U dxg
      let inCochain :=
        ConcreteCategory.hom ((cotangentXIso (structureMapLift p) (n + 1)).inv.val.app U)
          (ext :
            ((simplicialModule (inverseImageLift p) (Under.mk (structureMapLift p))).obj
              (op ⦋n + 1⦌)).val.obj U)
      let img :=
        ConcreteCategory.hom
          (((transitivityConnectingCochain p f).f (-(n + 1 : ℤ))).val.app U) inCochain
      let unshifted :=
        ConcreteCategory.hom
          ((CochainComplex.shiftFunctorObjXIso (pullbackCotangentCochain p f) (1 : ℤ)
              (-(n + 1 : ℤ)) (-n : ℤ) (transitivityConnecting_shiftEq n)).hom.val.app U)
            img
      (ConcreteCategory.hom
        (((extendAlong (structureMapLift p)).map
            (cotangentXIso (pulledMap p f) n).hom).val.app U) unshifted :
        (connectingTarget p f n).val.obj U) :=
  sorry

/-- Polynomial evaluation of the free `p⁻¹ 𝒪_X`-algebra on the previous `W/X` iterate at
the free-forgetful unit of `R_{n+1}`. -/
def connectingPolyEval {W X : AlgebraicSpace S} (p : W ⟶ X) (n : ℕ)
    (U : (smallEtaleSite W)ᵒᵖ) :
    MvPolynomial ((connectingGenerators p n).obj.obj U)
        ((inverseImageLift p).obj.obj U) →+*
      (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
        (op ⦋n + 1⦌)).right.obj.obj U :=
  let Rterm :=
    standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) (op ⦋n + 1⦌)
  -- Local instance justification (proof-local temporary data): sectionwise algebra
  -- structure of the degree-`n+1` `W/X` standard-resolution term over `p⁻¹ 𝒪_X`.
  letI := (Rterm.hom.hom.app U).hom.toAlgebra
  (MvPolynomial.aeval (S₁ := Rterm.right.obj.obj U)
      (fun b =>
        ((connectingGeneratorInclude p n).hom.app U b :
          Rterm.right.obj.obj U))).toRingHom

/-- Polynomial evaluation sends the variable of a previous-iterate section to the
corresponding free generator of `R_{n+1}`. -/
theorem connectingPolyEval_X {W X : AlgebraicSpace S} (p : W ⟶ X) (n : ℕ)
    (U : (smallEtaleSite W)ᵒᵖ) (b : (connectingGenerators p n).obj.obj U) :
    connectingPolyEval p n U (MvPolynomial.X b) =
      (connectingGeneratorInclude p n).hom.app U b :=
  sorry

/-- The sheaf-level `p⁻¹ 𝒪_X`-derivation on the free presentation of `R_{n+1}` with values
in `connectingTarget`, sending every free generator of the previous iterate to
`connectingGeneratorValue`. -/
def connectingPolyDerivation {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : ℕ) :
    (connectingTarget p f n).val.Derivation'
      (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
        (op ⦋n + 1⦌)).hom.hom :=
  let A := inverseImageLift p
  let E := connectingGenerators p n
  let Rterm :=
    standardTerm A (Under.mk (structureMapLift p)) (op ⦋n + 1⦌)
  let sqZeroPresheaf : (smallEtaleSite W)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
    { obj := fun U =>
        let Rsec := Rterm.right.obj.obj U
        let Msec := (connectingTarget p f n).val.obj U
        -- Local instance justification (proof-local temporary data): sectionwise opposite
        -- module and central scalar structure for the square-zero extension at `U`.
        letI := (Rterm.hom.hom.app U).hom.toAlgebra
        letI := Module.compHom Msec (Rterm.hom.hom.app U).hom
        letI :=
          Module.compHom Msec
            (RingHom.fromOpposite (RingHom.id Rsec) fun _ _ => Commute.all _ _)
        letI : IsCentralScalar Rsec Msec := sorry
        CommRingCat.of (TrivSqZeroExt Rsec Msec)
      map := fun {U V} i =>
        let RsecU := Rterm.right.obj.obj U
        let RsecV := Rterm.right.obj.obj V
        let MsecU := (connectingTarget p f n).val.obj U
        let MsecV := (connectingTarget p f n).val.obj V
        -- Local instance justification (proof-local temporary data): sectionwise opposite
        -- module and central scalar structure at the source and target of a restriction map.
        letI := (Rterm.hom.hom.app U).hom.toAlgebra
        letI := Module.compHom MsecU (Rterm.hom.hom.app U).hom
        letI :=
          Module.compHom MsecU
            (RingHom.fromOpposite (RingHom.id RsecU) fun _ _ => Commute.all _ _)
        letI : IsCentralScalar RsecU MsecU := sorry
        letI := (Rterm.hom.hom.app V).hom.toAlgebra
        letI := Module.compHom MsecV (Rterm.hom.hom.app V).hom
        letI :=
          Module.compHom MsecV
            (RingHom.fromOpposite (RingHom.id RsecV) fun _ _ => Commute.all _ _)
        letI : IsCentralScalar RsecV MsecV := sorry
        CommRingCat.ofHom
          { toFun := fun x =>
              ⟨ConcreteCategory.hom (Rterm.right.obj.map i) x.1,
                ConcreteCategory.hom ((connectingTarget p f n).val.map i) x.2⟩
            map_one' := sorry
            map_mul' := sorry
            map_zero' := sorry
            map_add' := sorry }
      map_id := sorry
      map_comp := sorry }
  let sqZeroSheaf : Sheaf (smallEtaleTopology W) CommRingCat.{u + 1} :=
    ⟨sqZeroPresheaf, sorry⟩
  let sqZeroBase : A ⟶ sqZeroSheaf :=
    ObjectProperty.homMk
      { app := fun U =>
          let Rsec := Rterm.right.obj.obj U
          let Msec := (connectingTarget p f n).val.obj U
          -- Local instance justification (proof-local temporary data): sectionwise opposite
          -- module and central scalar structure for the coefficient map into the square-zero
          -- extension.
          letI := (Rterm.hom.hom.app U).hom.toAlgebra
          letI := Module.compHom Msec (Rterm.hom.hom.app U).hom
          letI :=
            Module.compHom Msec
              (RingHom.fromOpposite (RingHom.id Rsec) fun _ _ => Commute.all _ _)
          letI : IsCentralScalar Rsec Msec := sorry
          CommRingCat.ofHom
            { toFun := fun a =>
                inl (ConcreteCategory.hom (Rterm.hom.hom.app U) a)
              map_one' := sorry
              map_mul' := sorry
              map_zero' := sorry
              map_add' := sorry }
        naturality := sorry }
  let sqZeroAssign : E ⟶ (sheafForget (smallEtaleTopology W)).obj sqZeroSheaf :=
    ObjectProperty.homMk
      { app := fun U =>
          TypeCat.ofHom fun b =>
          let Rsec := Rterm.right.obj.obj U
          let Msec := (connectingTarget p f n).val.obj U
          -- Local instance justification (proof-local temporary data): sectionwise opposite
          -- module and central scalar structure for the generator assignment.
          letI := (Rterm.hom.hom.app U).hom.toAlgebra
          letI := Module.compHom Msec (Rterm.hom.hom.app U).hom
          letI :=
            Module.compHom Msec
              (RingHom.fromOpposite (RingHom.id Rsec) fun _ _ => Commute.all _ _)
          letI : IsCentralScalar Rsec Msec := sorry
          (⟨(connectingGeneratorInclude p n).hom.app U b,
              connectingGeneratorValue p f n b⟩ : TrivSqZeroExt Rsec Msec)
        naturality := sorry }
  let sqZeroEval :=
    evaluation (Under.mk sqZeroBase) E sqZeroAssign
  PresheafOfModules.Derivation'.mk
    (fun U =>
      let Rsec := Rterm.right.obj.obj U
      let Msec := (connectingTarget p f n).val.obj U
      -- Local instance justification (proof-local temporary data): sectionwise opposite
      -- module and central scalar structure so the square-zero evaluation lands in
      -- `connectingTarget`.
      letI := (Rterm.hom.hom.app U).hom.toAlgebra
      letI := Module.compHom Msec (Rterm.hom.hom.app U).hom
      letI :=
        Module.compHom Msec
          (RingHom.fromOpposite (RingHom.id Rsec) fun _ _ => Commute.all _ _)
      letI : IsCentralScalar Rsec Msec := sorry
      ModuleCat.Derivation.mk
        (fun x =>
          snd (ConcreteCategory.hom (sqZeroEval.right.hom.app U) x))
        sorry sorry sorry)
    sorry

/-- Polynomial-model Kähler map sending each free generator of `R_{n+1}` to the
transitivity boundary of that generator in the extended degree-`n` `X/B` term. -/
def connectingPolyHom {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) (n : ℕ) :
    differentialsOn
        (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
          (op ⦋n + 1⦌)).hom ⟶
      connectingTarget p f n :=
  relativeDifferentialDesc
    (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p)) (op ⦋n + 1⦌)).hom
    (connectingPolyDerivation p f n)

/-- Unfolding of `connectingPolyHom` as universal descent of `connectingPolyDerivation`. -/
theorem connectingPolyHom_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : ℕ) :
    connectingPolyHom p f n =
      relativeDifferentialDesc
        (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
          (op ⦋n + 1⦌)).hom
        (connectingPolyDerivation p f n) :=
  sorry

/-- Comparison of `Ω_{R_{n+1}/X}` with the restricted extended degree-`n` `X/B` term,
via the standard-resolution Kähler derivation. -/
def connectingKaehlerToRestrict {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : ℕ) :
    differentialsOn
        (standardTerm (inverseImageLift p) (Under.mk (structureMapLift p))
          (op ⦋n + 1⦌)).hom ⟶
      connectingTarget p f n :=
  connectingPolyHom p f n

/-- Unfolding of `connectingKaehlerToRestrict` as `connectingPolyHom`. -/
theorem connectingKaehlerToRestrict_eq {W X B : AlgebraicSpace S} (p : W ⟶ X)
    (f : X ⟶ B) (n : ℕ) :
    connectingKaehlerToRestrict p f n = connectingPolyHom p f n :=
  sorry

/-- Native simplicial transitivity boundary
`Ω_{R_{n+1}/X} ⊗ 𝒪_W ⟶ (Ω_{P_n/B} ⊗ 𝒪_X) ⊗ 𝒪_W` in every simplicial degree, as an
`𝒪_W`-module map obtained by extending the standard-resolution Kähler derivation along
the augmentation of `R_{n+1}` (and thence along `structureMapLift p`). -/
def connectingSimplicialBoundary {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n : ℕ) :
    (simplicialModule (inverseImageLift p) (Under.mk (structureMapLift p))).obj
        (op ⦋n + 1⦌) ⟶
      (extendAlong (structureMapLift p)).obj
        ((simplicialModule (pulledInverseImage p f) (Under.mk (pulledMap p f))).obj
          (op ⦋n⦌)) :=
  ((extendRestrictAdj
        (standardAugmentation (inverseImageLift p) (Under.mk (structureMapLift p))
          (op ⦋n + 1⦌))).homEquiv _ _).symm
    (connectingKaehlerToRestrict p f n)

/-- Degreewise transitivity boundary, nonzero only when the simplicial degrees differ by `1`. -/
def connectingSimplicialMap {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (n m : ℕ) :
    (simplicialModule (inverseImageLift p) (Under.mk (structureMapLift p))).obj (op ⦋n⦌) ⟶
      (extendAlong (structureMapLift p)).obj
        ((simplicialModule (pulledInverseImage p f) (Under.mk (pulledMap p f))).obj (op ⦋m⦌)) :=
  if h : n = m + 1 then
    eqToHom
        (congrArg
          (fun k : ℕ =>
            (simplicialModule (inverseImageLift p) (Under.mk (structureMapLift p))).obj
              (op ⦋k⦌))
          h) ≫
      connectingSimplicialBoundary p f m
  else
    0

/-- The cochain-level components of the mapping-cone comparison, in every cohomological
degree. -/
def connectingPredMap {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) (i : ℤ) :
    (cotangentCochain p).X i ⟶ (pullbackCotangentCochain p f).X (i + 1) :=
  match hs : embeddingDownNat.r i, ht : embeddingDownNat.r (i + 1) with
  | some n, some m =>
      (extendXIso
          ((alternatingFaceMapComplex
              (SheafOfModules.{u + 1} (ringOf (commStructureSheafLift W)))).obj
            (simplicialModule (inverseImageLift p) (Under.mk (structureMapLift p))))
          embeddingDownNat
          (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) hs)).hom ≫
        connectingSimplicialMap p f n m ≫
        (extendAlong (structureMapLift p)).map
          (extendXIso
              ((alternatingFaceMapComplex
                  (SheafOfModules.{u + 1} (ringOf (inverseImageLift p)))).obj
                (simplicialModule (pulledInverseImage p f) (Under.mk (pulledMap p f))))
              embeddingDownNat
              (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) ht)).inv
  | _, _ => 0

/-- Comparison of `L_{W/X}` into the mapping cone of the first transitivity map. -/
def toMappingConeCochain {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    cotangentCochain p ⟶ mappingCone (transitivityMapCochain p f) where
  f i :=
    connectingPredMap p f i ≫
      (mappingCone.inl (transitivityMapCochain p f)).v (i + 1) i
        (add_neg_cancel_right i (1 : ℤ))
  comm' := sorry

/-- Unfolding of `toMappingConeCochain` by including the connecting components along
`mappingCone.inl`. -/
theorem toMappingConeCochain_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B)
    (i : ℤ) :
    (toMappingConeCochain p f).f i =
      connectingPredMap p f i ≫
        (mappingCone.inl (transitivityMapCochain p f)).v (i + 1) i
          (add_neg_cancel_right i (1 : ℤ)) :=
  sorry

/-- The connecting map `L_{W/X} ⟶ (Lp^* L_{X/B})⟦1⟧` of the transitivity triangle. -/
def connectingMap {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    cotangent p ⟶ (pullbackCotangent p f)⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (toMappingConeCochain p f) ≫
    DerivedCategory.Q.map (mappingCone.triangle (transitivityMapCochain p f)).mor₃ ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (pullbackCotangentCochain p f)

/-- Unfolding of `connectingMap` as `Q.map` of the mapping-cone comparison composed with
`mappingCone.triangle.mor₃` and `DerivedCategory.Q.commShiftIso 1`. -/
theorem connectingMap_eq {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    connectingMap p f =
      DerivedCategory.Q.map (toMappingConeCochain p f) ≫
        DerivedCategory.Q.map (mappingCone.triangle (transitivityMapCochain p f)).mor₃ ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app (pullbackCotangentCochain p f) :=
  sorry

/-- The transitivity triangle of `W ⟶ X ⟶ B` in `D(𝒪_W)`. -/
def transitivityTriangle {W X B : AlgebraicSpace S} (p : W ⟶ X) (f : X ⟶ B) :
    Triangle (DerivedCategory (CommModules W)) :=
  Triangle.mk (transitivityMap p f) (toRelativeMap p f) (connectingMap p f)

/-- The transitivity triangle of `W ⟶ X ⟶ B` is distinguished in `D(𝒪_W)`. -/
theorem transitivityTriangle_distinguished {W X B : AlgebraicSpace S}
    (p : W ⟶ X) (f : X ⟶ B) :
    transitivityTriangle p f ∈ distTriang (DerivedCategory (CommModules W)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Cotangent
