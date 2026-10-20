/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion.Exact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Boundary
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.StructureSheaf
public import Mathlib.CategoryTheory.Subobject.Limits
public import stacks_project.Chap98.Definition_98_22_1_DeformationSituation
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
public import ReasLib.RingTheory.RingHom.SquareZero
public import stacks_project.Chap98.Example_98_22_3_BaseChange

/-!
# Obstruction modules and connecting classes for global-sections deformations

For an affine value `x ∈ Γ(W_A, F_A)`, the obstruction functor sends an `A`-module `M` to
`H^1(W_A, F_A ⊗_A M)`. A square-zero extension `A' → A` supplies the unpulled short exact
sequence of the closed immersion `W_A ⟶ W_{A'}`, and the obstruction class of `x` is the
connecting image of `x` transported into `H^1(W_A, F_A ⊗_A I)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace TopCat
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.GlobalSections

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable {W : Scheme.{u}} (w : W ⟶ S Λ)
variable (F : W.Modules)

/-- The sheaf `F_A ⊗_A M` on `W_A`, obtained by pulling `M^~` back from `Spec(A)` and tensoring
with `F_A`. -/
def tensorModule (A : Type u) [CommRing A] [Algebra Λ A] (M : ModuleCat A) :
    (affineBaseChange w A).Modules :=
  tensorObj (affineModulePullback w F A)
    ((Scheme.Modules.pullback (baseChangeFst w (specOver Λ A))).obj
      ((tilde.functor (CommRingCat.of A)).obj M))

/-- `tensorModule` is the tensor of `F_A` with the pullback of `M^~`. -/
theorem tensorModule_obj (A : Type u) [CommRing A] [Algebra Λ A] (M : ModuleCat A) :
    tensorModule w F A M =
      tensorObj (affineModulePullback w F A)
        ((Scheme.Modules.pullback (baseChangeFst w (specOver Λ A))).obj
          ((tilde.functor (CommRingCat.of A)).obj M)) :=
  sorry

/-- A morphism of `A`-modules induces a morphism of the associated tensor sheaves on `W_A`. -/
def tensorModuleMap (A : Type u) [CommRing A] [Algebra Λ A] {M N : ModuleCat A} (f : M ⟶ N) :
    tensorModule w F A M ⟶ tensorModule w F A N :=
  tensorHom (𝟙 (affineModulePullback w F A))
    ((Scheme.Modules.pullback (baseChangeFst w (specOver Λ A))).map
      ((tilde.functor (CommRingCat.of A)).map f))

/-- Degree-`p` cohomology of modules on `W_A`, as `A`-modules via `W_A ⟶ Spec(A)`. -/
abbrev cohomologyMod (A : Type u) [CommRing A] [Algebra Λ A] (p : ℕ) :
    (affineBaseChange w A).Modules ⥤ ModuleCat A :=
  Scheme.Hom.cohomologyFunctor (baseChangeFst w (specOver Λ A)) p

/-- The obstruction functor `O_x`, sending `M` to `H^1(W_A, F_A ⊗_A M)`. The section `x` is
not used in the formula. -/
def obstructionModule (A : Type u) [CommRing A] [Algebra Λ A] :
    ModuleCat A ⥤ ModuleCat A where
  obj M := (cohomologyMod w A 1).obj (tensorModule w F A M)
  map {M N} f := (cohomologyMod w A 1).map (tensorModuleMap w F A f)
  map_id := sorry
  map_comp := sorry

/-- Evaluating the obstruction functor on `M` recovers `H^1(W_A, F_A ⊗_A M)`. -/
theorem obstructionModule_obj (A : Type u) [CommRing A] [Algebra Λ A] (M : ModuleCat A) :
    (obstructionModule w F A).obj M = (cohomologyMod w A 1).obj (tensorModule w F A M) :=
  sorry

/-- The kernel `I = Ker(A' → A)` as an object of `ModuleCat A`. -/
abbrev kernelModule (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A' A]
    [(algebraMap A' A).IsSquareZeroExtension] : ModuleCat A :=
  ModuleCat.of A (RingHom.ker (algebraMap A' A))

/-- `kernelModule` is the kernel of `algebraMap A' A`, as an `A`-module. -/
theorem kernelModule_obj (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    kernelModule A A' = ModuleCat.of A (RingHom.ker (algebraMap A' A)) :=
  sorry

/-- The kernel-universal inclusion `I ↪ A'` as `A'`-modules, from the square-zero kernel
viewed by restriction of scalars. -/
def kernelRestrictInclusion (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra A' A] [(algebraMap A' A).IsSquareZeroExtension] :
    (ModuleCat.restrictScalars (algebraMap A' A)).obj (kernelModule A A') ⟶
      ModuleCat.of A' A' :=
  ModuleCat.homMk
    (AddCommGrpCat.ofHom (RingHom.ker (algebraMap A' A)).toAddSubgroup.subtype)
    (fun _ ↦ sorry)

/-- The ideal sheaf of `Spec.map (algebraMap A' A)` on `Spec(A')`. -/
def specMapIdealSheaf (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    (Spec (CommRingCat.of A')).Modules :=
  RingedSpace.Hom.idealSheaf (Spec.map (CommRingCat.ofHom (algebraMap A' A))).toShHom

/-- The structure-sheaf map whose kernel is `specMapIdealSheaf`. -/
abbrev specMapKernelMap (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :=
  SheafOfModules.RingedSite.KernelIdeal.map
    (RingedSpace.Hom.commRingSheafPushforwardMap
      (Spec.map (CommRingCat.ofHom (algebraMap A' A))).toShHom)

/-- The associated-sheaf map `I^~ → O` vanishes on `i_* O`. -/
theorem specMapTildeToUnit_comp_eq_zero (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra A' A] [(algebraMap A' A).IsSquareZeroExtension] :
    (tilde.functor (CommRingCat.of A')).map (kernelRestrictInclusion A A') ≫
        specMapKernelMap A A' = 0 :=
  sorry

/-- Kernel-universal comparison `tilde_{A'}(restrictScalars I) ⟶ idealSheaf(Spec.map (A' → A))`,
from `I ↪ A'` and vanishing into `i_* O`. -/
def specMapTildeToIdealSheaf (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra A' A] [(algebraMap A' A).IsSquareZeroExtension] :
    (tilde.functor (CommRingCat.of A')).obj
        ((ModuleCat.restrictScalars (algebraMap A' A)).obj (kernelModule A A')) ⟶
      specMapIdealSheaf A A' :=
  kernel.lift (specMapKernelMap A A')
      ((tilde.functor (CommRingCat.of A')).map (kernelRestrictInclusion A A'))
      (specMapTildeToUnit_comp_eq_zero A A') ≫
    (kernelSubobjectIso (specMapKernelMap A A')).inv

/-- On affine spectra, the associated sheaf of the kernel is the ideal sheaf of `Spec.map`. -/
instance specMapTildeToIdealSheaf_isIso (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra A' A] [(algebraMap A' A).IsSquareZeroExtension] :
    IsIso (specMapTildeToIdealSheaf A A') :=
  sorry

/-- The kernel-universal comparison as an isomorphism. -/
def specMapTildeToIdealSheafIso (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra A' A] [(algebraMap A' A).IsSquareZeroExtension] :
    (tilde.functor (CommRingCat.of A')).obj
        ((ModuleCat.restrictScalars (algebraMap A' A)).obj (kernelModule A A')) ≅
      specMapIdealSheaf A A' :=
  asIso (specMapTildeToIdealSheaf A A')

/-- The canonical short exact sequence of the thickening `W_A ⟶ W_{A'}`, as a complex on
`W_{A'}`. -/
def obstructionSequence (A A' : Type u) [CommRing A] [CommRing A'] [Algebra Λ A] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A] [(algebraMap A' A).IsSquareZeroExtension] :
    ShortComplex (affineBaseChange w A').Modules :=
  Scheme.Modules.ClosedImmersion.sequence (thickeningHom w A A')
    (affineModulePullback w F A')

/-- Flatness of `F` over `S` makes the unpulled obstruction sequence short exact. -/
theorem obstructionSequence_shortExact (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (hflat : Scheme.Modules.flatOver F w) :
    (obstructionSequence w F A A').ShortExact :=
  sorry

/-- The comparison identifying `F_A` with `i^* F_{A'}` along `W_A ⟶ W_{A'}`. -/
def affineModuleIso (A A' : Type u) [CommRing A] [CommRing A'] [Algebra Λ A] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A] :
    affineModulePullback w F A ≅
      (Scheme.Modules.pullback (thickeningHom w A A')).obj (affineModulePullback w F A') :=
  ((Scheme.Modules.pullbackCongr (baseChangeMap_snd w (specOverMap Λ A A'))).app F).symm ≪≫
    ((Scheme.Modules.pullbackComp (thickeningHom w A A')
        (baseChangeSnd w (specOver Λ A'))).app F).symm

/-- `affineModuleIso` is the pullback-composition comparison of `F_A` with `i^* F_{A'}`. -/
theorem affineModuleIso_hom (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A] :
    (affineModuleIso w F A A').hom = modulePullbackMap w F (specOverMap Λ A A') :=
  sorry

/-- Global sections of the third term of `obstructionSequence` agree with global sections
of `i^* F_{A'}`, via `Γ(i_* G, ⊤) = Γ(G, ⊤)`. -/
theorem obstructionSequence_x3_sections (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    Γ((obstructionSequence w F A A').X₃, ⊤) =
      Γ((Scheme.Modules.pullback (thickeningHom w A A')).obj
        (affineModulePullback w F A'), ⊤) :=
  rfl

/-- Transport of a global section of `F_A` to a global section of the third term of
`obstructionSequence`, using `Γ(i_* G, ⊤) = Γ(G, ⊤)` and `F_A ≅ i^* F_{A'}`. -/
def toObstructionSequenceX3 (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (x : Γ(affineModulePullback w F A, ⊤)) :
    Γ((obstructionSequence w F A A').X₃, ⊤) :=
  (obstructionSequence_x3_sections w F A A').symm ▸
    sectionsHom (affineModuleIso w F A A').hom x

/-- `toObstructionSequenceX3` applies the identification `F_A ≅ i^* F_{A'}` on global sections. -/
theorem toObstructionSequenceX3_eq (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (x : Γ(affineModulePullback w F A, ⊤)) :
    toObstructionSequenceX3 w F A A' x =
      (obstructionSequence_x3_sections w F A A').symm ▸
        sectionsHom (affineModuleIso w F A A').hom x :=
  sorry

/-- The identification of the pulled kernel sheaf `i^*(I_W ⊗ F_{A'})` with `F_A ⊗ i^* I_W`. -/
def obstructionKernelTensorIso (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    (Scheme.Modules.pullback (thickeningHom w A A')).obj (obstructionSequence w F A A').X₁ ≅
      tensorObj (affineModulePullback w F A)
        ((Scheme.Modules.pullback (thickeningHom w A A')).obj
          (RingedSpace.Hom.idealSheaf (thickeningHom w A A').toShHom)) :=
  Scheme.Modules.pullbackTensorIso (thickeningHom w A A')
      (RingedSpace.Hom.idealSheaf (thickeningHom w A A').toShHom)
      (affineModulePullback w F A') ≪≫
    tensorIso (Iso.refl _) (affineModuleIso w F A A').symm ≪≫
    (β_ _ _).symm

/-- The structure-sheaf map whose kernel is the thickening ideal sheaf on `W_{A'}`. -/
abbrev thickeningKernelMap (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :=
  SheafOfModules.RingedSite.KernelIdeal.map
    (RingedSpace.Hom.commRingSheafPushforwardMap (thickeningHom w A A').toShHom)

/-- The pulled spectrum ideal sheaf maps to `O_{W_{A'}}` by the ideal inclusion and the
structure-sheaf pullback comparison. -/
def pullbackSpecIdealToUnit (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    (Scheme.Modules.pullback (baseChangeFst w (specOver Λ A'))).obj (specMapIdealSheaf A A') ⟶
      SheafOfModules.unit (affineBaseChange w A').ringCatSheaf :=
  (Scheme.Modules.pullback (baseChangeFst w (specOver Λ A'))).map
      (RingedSpace.Hom.idealSheafι
        (Spec.map (CommRingCat.ofHom (algebraMap A' A))).toShHom) ≫
    (Scheme.Modules.pullbackStructureSheafIso
      (baseChangeFst w (specOver Λ A'))).hom

/-- The pulled spectrum ideal sheaf vanishes in `i_* O_{W_A}`. -/
theorem pullbackSpecIdealToUnit_comp_eq_zero (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    pullbackSpecIdealToUnit w A A' ≫ thickeningKernelMap w A A' = 0 :=
  sorry

/-- Base-change comparison in the kernel-lift direction:
`(Modules.pullback (W_{A'} ⟶ Spec(A'))).obj (idealSheaf(Spec.map)) ⟶ idealSheaf(thickeningHom)`. -/
def pullbackSpecIdealToThickening (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    (Scheme.Modules.pullback (baseChangeFst w (specOver Λ A'))).obj (specMapIdealSheaf A A') ⟶
      RingedSpace.Hom.idealSheaf (thickeningHom w A A').toShHom :=
  kernel.lift (thickeningKernelMap w A A') (pullbackSpecIdealToUnit w A A')
      (pullbackSpecIdealToUnit_comp_eq_zero w A A') ≫
    (kernelSubobjectIso (thickeningKernelMap w A A')).inv

/-- For the pullback square of a first-order thickening, the kernel-lift comparison is an
isomorphism. -/
instance pullbackSpecIdealToThickening_isIso (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    IsIso (pullbackSpecIdealToThickening w A A') :=
  sorry

/-- Base-change comparison `idealSheaf(thickeningHom) ≅ pullback of idealSheaf(Spec.map)`. -/
def thickeningIdealSheafIso (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    RingedSpace.Hom.idealSheaf (thickeningHom w A A').toShHom ≅
      (Scheme.Modules.pullback (baseChangeFst w (specOver Λ A'))).obj
        (specMapIdealSheaf A A') :=
  (asIso (pullbackSpecIdealToThickening w A A')).symm

/-- Comparison of the pulled thickening ideal with the pullback of `I^~` from `Spec(A)`,
using the kernel-universal and base-change comparisons, affine tilde change of rings, and
the extend-restrict counit. -/
def obstructionConormalToTilde (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    (Scheme.Modules.pullback (thickeningHom w A A')).obj
        (RingedSpace.Hom.idealSheaf (thickeningHom w A A').toShHom) ⟶
      (Scheme.Modules.pullback (baseChangeFst w (specOver Λ A))).obj
        ((tilde.functor (CommRingCat.of A)).obj (kernelModule A A')) :=
  (Scheme.Modules.pullback (thickeningHom w A A')).map
      (thickeningIdealSheafIso w A A').hom ≫
    (Scheme.Modules.pullback (thickeningHom w A A')).map
      ((Scheme.Modules.pullback (baseChangeFst w (specOver Λ A'))).map
        (specMapTildeToIdealSheafIso A A').inv) ≫
    (Scheme.Modules.pullbackComp (thickeningHom w A A')
        (baseChangeFst w (specOver Λ A'))).hom.app
      ((tilde.functor (CommRingCat.of A')).obj
        ((ModuleCat.restrictScalars (algebraMap A' A)).obj (kernelModule A A'))) ≫
    (Scheme.Modules.pullbackCongr (baseChangeMap_fst w (specOverMap Λ A A'))).hom.app
      ((tilde.functor (CommRingCat.of A')).obj
        ((ModuleCat.restrictScalars (algebraMap A' A)).obj (kernelModule A A'))) ≫
    (Scheme.Modules.pullbackComp (baseChangeFst w (specOver Λ A))
        (Spec.map (CommRingCat.ofHom (algebraMap A' A)))).inv.app
      ((tilde.functor (CommRingCat.of A')).obj
        ((ModuleCat.restrictScalars (algebraMap A' A)).obj (kernelModule A A'))) ≫
    (Scheme.Modules.pullback (baseChangeFst w (specOver Λ A))).map
      ((tilde.ChangeOfRings.Pullback.iso
          (CommRingCat.ofHom (algebraMap A' A))).hom.app
        ((ModuleCat.restrictScalars (algebraMap A' A)).obj (kernelModule A A'))) ≫
    (Scheme.Modules.pullback (baseChangeFst w (specOver Λ A))).map
      ((tilde.functor (CommRingCat.of A)).map
        ((ModuleCat.extendRestrictScalarsAdj (algebraMap A' A)).counit.app
          (kernelModule A A')))

/-- The comparison morphism from `i^*(I_W ⊗ F_{A'})` to `F_A ⊗_A I^~`. -/
def obstructionKernelComparison (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    (Scheme.Modules.pullback (thickeningHom w A A')).obj (obstructionSequence w F A A').X₁ ⟶
      tensorModule w F A (kernelModule A A') :=
  (obstructionKernelTensorIso w F A A').hom ≫
    tensorHom (𝟙 (affineModulePullback w F A)) (obstructionConormalToTilde w A A')

/-- `obstructionKernelComparison` is the tensor of `F_A` with the tilde comparison of the
pulled thickening ideal. -/
theorem obstructionKernelComparison_eq (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    obstructionKernelComparison w F A A' =
      (obstructionKernelTensorIso w F A A').hom ≫
        tensorHom (𝟙 (affineModulePullback w F A)) (obstructionConormalToTilde w A A') :=
  sorry

/-- The connecting image of `x` in `H^1(W_{A'}, I_W ⊗ F_{A'})`. -/
def obstructionConnectingClass (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (hS : (obstructionSequence w F A A').ShortExact)
    (x : Γ(affineModulePullback w F A, ⊤)) :
    Scheme.Hom.cohomology (baseChangeFst w (specOver Λ A'))
      (obstructionSequence w F A A').X₁ 1 :=
  Scheme.Hom.cohomologyBoundaryFromExt (baseChangeFst w (specOver Λ A')) hS
    (toObstructionSequenceX3 w F A A' x)

/-- Direct-image cohomology of a module on `W_A`, as an additive sheaf on `W_{A'}`. -/
def obstructionPushforwardToSheaf (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (G : (affineBaseChange w A).Modules) :
    (SheafOfModules.toSheaf (affineBaseChange w A').ringCatSheaf).obj
        ((Scheme.Modules.pushforward (thickeningHom w A A')).obj G) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (thickeningHom w A A').base).obj
        ((SheafOfModules.toSheaf (affineBaseChange w A).ringCatSheaf).obj G) :=
  𝟙 _

/-- The adjunction unit `X₁ ⟶ i_* i^* X₁` on the unpulled obstruction sequence. -/
def obstructionSequenceUnit (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    (obstructionSequence w F A A').X₁ ⟶
      (Scheme.Modules.pushforward (thickeningHom w A A')).obj
        ((Scheme.Modules.pullback (thickeningHom w A A')).obj
          (obstructionSequence w F A A').X₁) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (thickeningHom w A A')).unit.app
    (obstructionSequence w F A A').X₁

/-- Pullback of the connecting class along `W_A ⟶ W_{A'}` into `H^1(W_A, i^*(I_W ⊗ F_{A'}))`,
by cohomology of the adjunction unit followed by the canonical direct-image comparison. -/
def obstructionConnectingPullback (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (y : Scheme.Hom.cohomology (baseChangeFst w (specOver Λ A'))
      (obstructionSequence w F A A').X₁ 1) :
    Scheme.Hom.cohomology (baseChangeFst w (specOver Λ A))
      ((Scheme.Modules.pullback (thickeningHom w A A')).obj
        (obstructionSequence w F A A').X₁) 1 :=
  (eqToHom (Scheme.Hom.cohomologyForget_obj_eq (baseChangeFst w (specOver Λ A))
        ((Scheme.Modules.pullback (thickeningHom w A A')).obj
          (obstructionSequence w F A A').X₁) 1).symm).hom
    ((CategoryTheory.Sheaf.pushforwardCohomologyMap
        (thickeningHom w A A').base
        ((SheafOfModules.toSheaf (affineBaseChange w A).ringCatSheaf).obj
          ((Scheme.Modules.pullback (thickeningHom w A A')).obj
            (obstructionSequence w F A A').X₁))
        1 ⊤).hom
      ((CategoryTheory.Sheaf.cohomologyMap
          (obstructionPushforwardToSheaf w A A'
            ((Scheme.Modules.pullback (thickeningHom w A A')).obj
              (obstructionSequence w F A A').X₁))
          1 ⊤).hom
        ((eqToHom (Scheme.Hom.cohomologyForget_obj_eq (baseChangeFst w (specOver Λ A'))
            ((Scheme.Modules.pushforward (thickeningHom w A A')).obj
              ((Scheme.Modules.pullback (thickeningHom w A A')).obj
                (obstructionSequence w F A A').X₁)) 1)).hom
          (((cohomologyMod w A' 1).map (obstructionSequenceUnit w F A A')).hom y))))

/-- The obstruction class of a global section `x` of `F_A` along a square-zero extension
`A' → A`, as an element of `O_x(I) = H^1(W_A, F_A ⊗_A I)`. -/
def obstructionClass (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (hflat : Scheme.Modules.flatOver F w)
    (x : Γ(affineModulePullback w F A, ⊤)) :
    (obstructionModule w F A).obj (kernelModule A A') :=
  ((cohomologyMod w A 1).map (obstructionKernelComparison w F A A')).hom
    (obstructionConnectingPullback w F A A'
      (obstructionConnectingClass w F A A'
        (obstructionSequence_shortExact w F A A' hflat) x))

/-- The obstruction class is the image of `x` under `cohomologyBoundaryFromExt` on `W_{A'}`,
transported by cohomology of the adjunction unit, the direct-image comparison, and the
comparison `i^*(I_W ⊗ F_{A'}) ⟶ F_A ⊗_A I^~`. -/
theorem obstructionClass_spec (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (hflat : Scheme.Modules.flatOver F w)
    (x : Γ(affineModulePullback w F A, ⊤)) :
    obstructionClass w F A A' hflat x =
      ((cohomologyMod w A 1).map (obstructionKernelComparison w F A A')).hom
        (obstructionConnectingPullback w F A A'
          (Scheme.Hom.cohomologyBoundaryFromExt (baseChangeFst w (specOver Λ A'))
            (obstructionSequence_shortExact w F A A' hflat)
            (toObstructionSequenceX3 w F A A' x))) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.GlobalSections
