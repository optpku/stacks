module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.Algebra.Category.CommRing.Internal
public import ReasLib.Algebra.Category.CommRing.Sheaf.Internal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension.Module
public import stacks_project.Chap66.Lemma_66_28_1_Hom
public import stacks_project.Chap70.Lemma_70_5_6_GlobalSections
public import stacks_project.Chap76.Lemma_76_18_1_Thickening

/-!
# Square-zero algebras on the small étale site of an algebraic space

A locally surjective square-zero extension of `𝒪_X` on `X_étale` has a canonical
quasi-coherent kernel module. Inverse image of commutative-ring sheaves along morphisms
of algebraic spaces is used to compare `f⁻¹𝒪_B`-algebra structures on first-order
thickenings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalCommRing
open CategoryTheory.Sheaf.InternalRing
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Commutative-ring-valued weak sheafification exists on the small étale site. -/
instance smallEtaleTopology_hasWeakSheafify_commRing {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) CommRingCat.{u} :=
  sorry

/-- On the small étale topology of an algebraic space, sheafification equivalences of
commutative-ring sheaves are the locally bijective morphisms. -/
instance smallEtaleTopology_wEqualsLocallyBijective_commRing {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (smallEtaleTopology X).WEqualsLocallyBijective CommRingCat.{u} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension

variable {S : Scheme.{u}}

/-- Inverse image of a commutative-ring sheaf along a morphism of algebraic spaces. -/
def commSheafInverseImageObj {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} :=
  fromInternalObj.{u + 1, u, u}
    ((internalCommRingInverseImage h).obj (toInternalObj.{u + 1, u, u} R))

/-- `commSheafInverseImageObj h R` is internal inverse image of `R` along `h`. -/
theorem commSheafInverseImageObj_eq {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    commSheafInverseImageObj h R =
      fromInternalObj.{u + 1, u, u}
        ((internalCommRingInverseImage h).obj (toInternalObj.{u + 1, u, u} R)) :=
  rfl

/-- Inverse image of a morphism of commutative-ring sheaves along a morphism of algebraic
spaces. -/
def commSheafInverseImageMap {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    {R R' : Sheaf (smallEtaleTopology Y) CommRingCat.{u}} (α : R ⟶ R') :
    commSheafInverseImageObj h R ⟶ commSheafInverseImageObj h R' :=
  fromInternalMap.{u + 1, u, u}
    ((internalCommRingInverseImage h).map (toInternalMap.{u + 1, u, u} α))

/-- `commSheafInverseImageMap h α` is internal inverse image of `α` along `h`. -/
theorem commSheafInverseImageMap_eq {X Y : AlgebraicSpace S} (h : X ⟶ Y)
    {R R' : Sheaf (smallEtaleTopology Y) CommRingCat.{u}} (α : R ⟶ R') :
    commSheafInverseImageMap h α =
      fromInternalMap.{u + 1, u, u}
        ((internalCommRingInverseImage h).map (toInternalMap.{u + 1, u, u} α)) :=
  rfl

/-- The inverse-image structure sheaf `f⁻¹𝒪_Y` is inverse image of `𝒪_Y`. -/
theorem commInverseImageStructureSheaf_eq {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    commInverseImageStructureSheaf f =
      commSheafInverseImageObj f (commStructureSheaf Y) :=
  rfl

/-- Equal morphisms of algebraic spaces induce equal inverse-image structure sheaves. -/
def commInverseImageCongr {X Y : AlgebraicSpace S} {a b : X ⟶ Y} (h : a = b) :
    commInverseImageStructureSheaf a ≅ commInverseImageStructureSheaf b :=
  eqToIso (congrArg commInverseImageStructureSheaf h)

/-- `commInverseImageCongr` is `eqToIso` of congruence on `commInverseImageStructureSheaf`. -/
theorem commInverseImageCongr_eq {X Y : AlgebraicSpace S} {a b : X ⟶ Y} (h : a = b) :
    commInverseImageCongr h = eqToIso (congrArg commInverseImageStructureSheaf h) :=
  rfl

/-- Inverse image of types along a composite morphism of algebraic spaces. -/
def inverseImageCompIso {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y) :
    (morphismOfTopoi f).inverseImage ⋙ (morphismOfTopoi p).inverseImage ≅
      (morphismOfTopoi (p ≫ f)).inverseImage :=
  Adjunction.leftAdjointCompIso
    (morphismOfTopoi f).adjunction (morphismOfTopoi p).adjunction
    (morphismOfTopoi (p ≫ f)).adjunction (Modules.typePushforwardComp p f)

/-- `inverseImageCompIso` is the left-adjoint mate of `typePushforwardComp`. -/
theorem inverseImageCompIso_eq {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y) :
    inverseImageCompIso p f =
      Adjunction.leftAdjointCompIso
        (morphismOfTopoi f).adjunction (morphismOfTopoi p).adjunction
        (morphismOfTopoi (p ≫ f)).adjunction (Modules.typePushforwardComp p f) :=
  rfl

/-- Inverse image of internal commutative rings reassociates along composition. -/
def internalCommRingInverseImageCompIso {U X Y : AlgebraicSpace S}
    (p : U ⟶ X) (f : X ⟶ Y) :
    internalCommRingInverseImage f ⋙ internalCommRingInverseImage p ≅
      internalCommRingInverseImage (p ≫ f) :=
  (@mapCommRingOfFiniteProductsCompIso
      (Sheaf (smallEtaleTopology Y) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
      (Sheaf (smallEtaleTopology X) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
      (Sheaf (smallEtaleTopology U) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U))
      (morphismOfTopoi f).inverseImage inferInstance
      (morphismOfTopoi p).inverseImage inferInstance).symm ≪≫
    @mapCommRingOfFiniteProductsNatIso
      (Sheaf (smallEtaleTopology Y) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
      (Sheaf (smallEtaleTopology U) (Type u)) _ _
      (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U))
      ((morphismOfTopoi f).inverseImage ⋙ (morphismOfTopoi p).inverseImage)
      (morphismOfTopoi (p ≫ f)).inverseImage inferInstance inferInstance
      (inverseImageCompIso p f)

/-- Unfolding of `internalCommRingInverseImageCompIso`. -/
theorem internalCommRingInverseImageCompIso_eq {U X Y : AlgebraicSpace S}
    (p : U ⟶ X) (f : X ⟶ Y) :
    internalCommRingInverseImageCompIso p f =
      (@mapCommRingOfFiniteProductsCompIso
          (Sheaf (smallEtaleTopology Y) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
          (Sheaf (smallEtaleTopology X) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology X))
          (Sheaf (smallEtaleTopology U) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U))
          (morphismOfTopoi f).inverseImage inferInstance
          (morphismOfTopoi p).inverseImage inferInstance).symm ≪≫
        @mapCommRingOfFiniteProductsNatIso
          (Sheaf (smallEtaleTopology Y) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology Y))
          (Sheaf (smallEtaleTopology U) (Type u)) _ _
          (sheafBraidedCategory.{u + 1, u, u} (smallEtaleTopology U))
          ((morphismOfTopoi f).inverseImage ⋙ (morphismOfTopoi p).inverseImage)
          (morphismOfTopoi (p ≫ f)).inverseImage inferInstance inferInstance
          (inverseImageCompIso p f) :=
  rfl

/-- Inverse image of commutative-ring sheaves reassociates along composition. -/
def commSheafInverseImageCompIso {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    commSheafInverseImageObj p (commSheafInverseImageObj f R) ≅
      commSheafInverseImageObj (p ≫ f) R :=
  fromInternal.{u + 1, u, u}.mapIso
    ((internalCommRingInverseImage p).mapIso
        (fromToIso.{u + 1, u, u}.app
          ((internalCommRingInverseImage f).obj (toInternalObj.{u + 1, u, u} R))) ≪≫
      (internalCommRingInverseImageCompIso p f).app
        (toInternalObj.{u + 1, u, u} R))

/-- Unfolding of `commSheafInverseImageCompIso`. -/
theorem commSheafInverseImageCompIso_eq {U X Y : AlgebraicSpace S} (p : U ⟶ X) (f : X ⟶ Y)
    (R : Sheaf (smallEtaleTopology Y) CommRingCat.{u}) :
    commSheafInverseImageCompIso p f R =
      fromInternal.{u + 1, u, u}.mapIso
        ((internalCommRingInverseImage p).mapIso
            (fromToIso.{u + 1, u, u}.app
              ((internalCommRingInverseImage f).obj (toInternalObj.{u + 1, u, u} R))) ≪≫
          (internalCommRingInverseImageCompIso p f).app
            (toInternalObj.{u + 1, u, u} R)) :=
  rfl

/-- The `𝒪_B`-algebra structure map `sX⁻¹ 𝒪_B ⟶ i⁻¹ 𝒪_{X'}` of a thickening over `B`,
as sheaves of commutative rings on `X_étale`. -/
def algebraMap {B X X' : AlgebraicSpace S}
    (i : X ⟶ X') (sX : X ⟶ B) (sX' : X' ⟶ B) (h : i ≫ sX' = sX) :
    commInverseImageStructureSheaf sX ⟶ commInverseImageStructureSheaf i :=
  (commInverseImageCongr h.symm).hom ≫
    (commSheafInverseImageCompIso i sX' (commStructureSheaf B)).inv ≫
    commSheafInverseImageMap i (commInverseImageStructureSheafMap sX')

/-- `algebraMap` is the transport of `i⁻¹((sX')^♯)` along `sX⁻¹ ≅ i⁻¹ sX'⁻¹`. -/
theorem algebraMap_eq {B X X' : AlgebraicSpace S}
    (i : X ⟶ X') (sX : X ⟶ B) (sX' : X' ⟶ B) (h : i ≫ sX' = sX) :
    algebraMap i sX sX' h =
      (commInverseImageCongr h.symm).hom ≫
        (commSheafInverseImageCompIso i sX' (commStructureSheaf B)).inv ≫
        commSheafInverseImageMap i (commInverseImageStructureSheafMap sX') :=
  rfl

/-- The square-zero kernel of `π : A ⟶ 𝒪_X`, with its canonical module structure over `𝒪_X`. -/
abbrev kernelModule {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) :
    RingedSite.ModuleCat.{u} (commRingedSite X) :=
  @KernelIdeal.IsSquareZero.targetModule.{u + 1, u, u}
    (smallEtaleSite X) _ (smallEtaleTopology X) _ A (commStructureSheaf X) π
    _ _ _ _ hπ (KernelIdeal.quotientComparison_isIso π)

/-- `kernelModule π hπ` is the target module of the square-zero kernel of `π`. -/
theorem kernelModule_eq {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) :
    kernelModule π hπ =
      @KernelIdeal.IsSquareZero.targetModule.{u + 1, u, u}
        (smallEtaleSite X) _ (smallEtaleTopology X) _ A (commStructureSheaf X) π
        _ _ _ _ hπ (KernelIdeal.quotientComparison_isIso π) :=
  rfl

/-- The underlying additive sheaf of `kernelModule π hπ` is the kernel ideal sheaf of `π`. -/
def kernelModuleForgetIso {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) :=
  @KernelIdeal.IsSquareZero.targetModuleForgetIso.{u + 1, u, u}
    (smallEtaleSite X) _ (smallEtaleTopology X) _ A (commStructureSheaf X) π
    _ _ _ _ hπ (KernelIdeal.quotientComparison_isIso π)

/-- `kernelModuleForgetIso` is `targetModuleForgetIso` of the square-zero kernel. -/
theorem kernelModuleForgetIso_eq {X : AlgebraicSpace S}
    {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) :
    kernelModuleForgetIso π hπ =
      @KernelIdeal.IsSquareZero.targetModuleForgetIso.{u + 1, u, u}
        (smallEtaleSite X) _ (smallEtaleTopology X) _ A (commStructureSheaf X) π
        _ _ _ _ hπ (KernelIdeal.quotientComparison_isIso π) :=
  rfl

/-- A first-order thickening over `B` realizing a square-zero algebra `A` on `X_étale`. -/
structure IsRealization {B X : AlgebraicSpace S} (f : X ⟶ B)
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π)
    (α : commInverseImageStructureSheaf f ⟶ A)
    (hα : α ≫ π = commInverseImageStructureSheafMap f)
    {X' : AlgebraicSpace S} (i : X ⟶ X') (s' : X' ⟶ B)
    (φ : commInverseImageStructureSheaf i ⟶ A) : Prop where
  /-- The morphism `i` is a first-order thickening. -/
  isFirstOrder : IsFirstOrderThickening i
  /-- The thickening lies over `B` via `s'`. -/
  overBase : i ≫ s' = f
  /-- The comparison `φ : i⁻¹𝒪_{X'} ⟶ A` is an isomorphism. -/
  isIso : IsIso φ
  /-- The isomorphism is compatible with the surjections to `𝒪_X`. -/
  compatibleSurjection : φ ≫ π = commInverseImageStructureSheafMap i
  /-- The isomorphism is a morphism of `f⁻¹𝒪_B`-algebras. -/
  compatibleAlgebra : α = algebraMap i f s' overBase ≫ φ

/-- Assemble a realization from a first-order thickening over `B` and a compatible algebra
isomorphism. -/
def IsRealization.of {B X : AlgebraicSpace S} (f : X ⟶ B)
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π)
    (α : commInverseImageStructureSheaf f ⟶ A)
    (hα : α ≫ π = commInverseImageStructureSheafMap f)
    {X' : AlgebraicSpace S} (i : X ⟶ X') (s' : X' ⟶ B)
    (φ : commInverseImageStructureSheaf i ⟶ A)
    (h_first : IsFirstOrderThickening i) (h_over : i ≫ s' = f) (h_iso : IsIso φ)
    (h_surj : φ ≫ π = commInverseImageStructureSheafMap i)
    (h_alg : α = algebraMap i f s' h_over ≫ φ) :
    IsRealization f A π hπ α hα i s' φ where
  isFirstOrder := h_first
  overBase := h_over
  isIso := h_iso
  compatibleSurjection := h_surj
  compatibleAlgebra := h_alg

/-- Being a realization unpacks as a first-order thickening over `B` together with a
compatible algebra isomorphism. -/
theorem isRealization_iff {B X : AlgebraicSpace S} (f : X ⟶ B)
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π)
    (α : commInverseImageStructureSheaf f ⟶ A)
    (hα : α ≫ π = commInverseImageStructureSheafMap f)
    {X' : AlgebraicSpace S} (i : X ⟶ X') (s' : X' ⟶ B)
    (φ : commInverseImageStructureSheaf i ⟶ A) :
    IsRealization f A π hπ α hα i s' φ ↔
      IsFirstOrderThickening i ∧
        ∃ h_over : i ≫ s' = f,
          IsIso φ ∧ φ ≫ π = commInverseImageStructureSheafMap i ∧
            α = algebraMap i f s' h_over ≫ φ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
