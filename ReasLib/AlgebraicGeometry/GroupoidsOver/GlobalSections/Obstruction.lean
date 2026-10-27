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
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Boundary
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.StructureSheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObstructionTheory
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
public import ReasLib.RingTheory.RingHom.SquareZero
public import ReasLib.AlgebraicGeometry.GroupoidsOver.GlobalSections.Functor

/-!
# Obstructions to lifting global sections

The obstruction module is the first cohomology of the pulled-back module tensored with
an associated module sheaf. Square-zero extensions give connecting classes through the
pulled base-kernel tensor sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace TopCat
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

-- The module interface exposes canonical constructions while keeping their one-use maps private.
-- These compatibility settings affect visibility only, without adding mathematical instances.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u

namespace AlgebraicGeometry.GroupoidsOver.GlobalSections

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable {W : Scheme.{u}} (w : W ⟶ Spec (CommRingCat.of Λ))
variable (F : W.Modules)

/-- The tensor sheaf over an explicitly given affine test scheme. -/
def tensorOverSpec {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of Λ)) (M : ModuleCat A) :
    (baseChange w (Over.mk a)).Modules :=
  tensorObj (modulePullback w F (Over.mk a))
    ((Scheme.Modules.pullback (baseChangeFst w (Over.mk a))).obj
      ((tilde.functor (CommRingCat.of A)).obj M))

/-- The tensor-sheaf map induced by a map of modules over the affine test ring. -/
def tensorOverSpecMap {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of Λ))
    {M N : ModuleCat A} (f : M ⟶ N) : tensorOverSpec w F a M ⟶ tensorOverSpec w F a N :=
  tensorHom (𝟙 (modulePullback w F (Over.mk a)))
    ((Scheme.Modules.pullback (baseChangeFst w (Over.mk a))).map
      ((tilde.functor (CommRingCat.of A)).map f))

/-- The tensor-sheaf construction preserves identity maps. -/
theorem tensorFunctorOverSpec_map_id {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of Λ)) (M : ModuleCat A) :
    tensorOverSpecMap w F a (𝟙 M) = 𝟙 (tensorOverSpec w F a M) := sorry

/-- The tensor-sheaf construction preserves composition. -/
theorem tensorFunctorOverSpec_map_comp {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of Λ))
    {M N P : ModuleCat A} (f : M ⟶ N) (g : N ⟶ P) :
    tensorOverSpecMap w F a (f ≫ g) = tensorOverSpecMap w F a f ≫ tensorOverSpecMap w F a g := sorry

/-- The functor sending a module over an affine test ring to its tensor sheaf on the base change. -/
def tensorFunctorOverSpec {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of Λ)) :
    ModuleCat A ⥤ (baseChange w (Over.mk a)).Modules where
  obj := tensorOverSpec w F a
  map := tensorOverSpecMap w F a
  map_id := tensorFunctorOverSpec_map_id w F a
  map_comp := tensorFunctorOverSpec_map_comp w F a

/-- The obstruction-module functor over an explicit affine structure morphism. -/
def obstructionModuleOverSpec {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of Λ)) : ModuleCat A ⥤ ModuleCat A :=
  tensorFunctorOverSpec w F a ⋙ Scheme.Hom.cohomologyFunctor (baseChangeFst w (Over.mk a)) 1

/-- The obstruction-module functor is linear over the affine test ring. -/
instance obstructionModuleOverSpec_moduleLinear {A : Type u} [CommRing A]
    (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of Λ)) :
    (obstructionModuleOverSpec w F a).ModuleLinear A := sorry

section Extension

variable {A A' : Type u} [CommRing A] [CommRing A']
variable (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of Λ))
variable (a' : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of Λ))
variable (π : A' →+* A) [π.IsSquareZeroExtension]
variable (hπ : Spec.map (CommRingCat.ofHom π) ≫ a' = a)

/-- The map of affine test schemes associated to a compatible extension of rings. -/
def extensionOverMap : Over.mk a ⟶ Over.mk a' :=
  Over.homMk (Spec.map (CommRingCat.ofHom π)) hπ

/-- The map of base changes induced by an extension of affine test rings. -/
def extensionHom : baseChange w (Over.mk a) ⟶ baseChange w (Over.mk a') :=
  baseChangeMap w (extensionOverMap a a' π hπ)

/-- The square-zero kernel, with its descended module structure over the target ring. -/
abbrev kernelOverSpec : ModuleCat A := ModuleCat.of A (RingHom.ker π)

/-- Inclusion of the square-zero kernel is linear over the source ring. -/
private theorem kernelRestrictInclusion_smul (r : A') (x : RingHom.ker π) :
    ((π r • x : RingHom.ker π) : A') = r * (x : A') := sorry

/-- The kernel inclusion after restricting the descended scalar action. -/
private def kernelRestrictInclusion :
    (ModuleCat.restrictScalars π).obj (kernelOverSpec π) ⟶ ModuleCat.of A' A' :=
  ModuleCat.homMk (AddCommGrpCat.ofHom (RingHom.ker π).toAddSubgroup.subtype)
    (fun r ↦ by ext x; exact (kernelRestrictInclusion_smul π r x).symm)

/-- The pullback of the base kernel sheaf to the thickened base change. -/
def baseKernelSheaf : (baseChange w (Over.mk a')).Modules :=
  (Scheme.Modules.pullback (baseChangeFst w (Over.mk a'))).obj
    ((tilde.functor (CommRingCat.of A')).obj
      ((ModuleCat.restrictScalars π).obj (kernelOverSpec π)))

/-- The base kernel sheaf tensored with the pulled-back module on the thickened scheme. -/
def baseKernelTensor : (baseChange w (Over.mk a')).Modules :=
  tensorObj (baseKernelSheaf w a' π) (modulePullback w F (Over.mk a'))

/-- The tensor inclusion obtained from the base-kernel inclusion and the structure-module unitor. -/
def baseKernelTensorMap : baseKernelTensor w F a' π ⟶ modulePullback w F (Over.mk a') :=
  tensorHom
    ((Scheme.Modules.pullback (baseChangeFst w (Over.mk a'))).map
        ((tilde.functor (CommRingCat.of A')).map (kernelRestrictInclusion π) ≫
          (tildeSelf (R := CommRingCat.of A')).hom) ≫
      (Scheme.Modules.pullbackStructureSheafIso (baseChangeFst w (Over.mk a'))).hom)
    (𝟙 (modulePullback w F (Over.mk a'))) ≫
    tensorHom (RingedSpace.unitIsoTensorUnit (baseChange w (Over.mk a')).toRingedSpace).hom
      (𝟙 (modulePullback w F (Over.mk a'))) ≫
    (λ_ (modulePullback w F (Over.mk a'))).hom

/-- The restriction map to the pushforward of pullback along the extension morphism. -/
def extensionRestrictionMap : modulePullback w F (Over.mk a') ⟶
    (Scheme.Modules.pushforward (extensionHom w a a' π hπ)).obj
      ((Scheme.Modules.pullback (extensionHom w a a' π hπ)).obj
        (modulePullback w F (Over.mk a'))) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (extensionHom w a a' π hπ)).unit.app _

/-- The base-kernel tensor inclusion vanishes after restriction to the closed test scheme. -/
theorem obstructionSequenceOverSpec_complex :
    baseKernelTensorMap w F a' π ≫ extensionRestrictionMap w F a a' π hπ = 0 := sorry

/-- The three-term base-kernel tensor sequence over a compatible square-zero extension. -/
def obstructionSequenceOverSpec : ShortComplex (baseChange w (Over.mk a')).Modules :=
  ShortComplex.mk (baseKernelTensorMap w F a' π) (extensionRestrictionMap w F a a' π hπ)
    (obstructionSequenceOverSpec_complex w F a a' π hπ)

/-- Relative flatness makes the base-kernel tensor sequence short exact. -/
theorem obstructionSequenceOverSpec_shortExact (hflat : Scheme.Modules.flatOver F w) :
    (obstructionSequenceOverSpec w F a a' π hπ).ShortExact := sorry

/-- Pullback composition identifies the module over the closed test scheme with the pulled thickened module. -/
def moduleIsoOverSpec : modulePullback w F (Over.mk a) ≅
    (Scheme.Modules.pullback (extensionHom w a a' π hπ)).obj (modulePullback w F (Over.mk a')) :=
  ((Scheme.Modules.pullbackCongr (baseChangeMap_snd w (extensionOverMap a a' π hπ))).symm ≪≫
    (Scheme.Modules.pullbackComp (extensionHom w a a' π hπ)
      (baseChangeSnd w (Over.mk a'))).symm).app F

-- Definitional comparison of the natural pullback isomorphisms requires a larger kernel budget.
set_option maxHeartbeats 4000000 in
omit [π.IsSquareZeroExtension] in
/-- The forward pullback-composition isomorphism is the canonical module pullback comparison. -/
private theorem moduleIsoOverSpec_hom :
    (moduleIsoOverSpec w F a a' π hπ).hom =
      modulePullbackMap w F (extensionOverMap a a' π hπ) := rfl

/-- The tensor comparison for the pullback of the base-kernel term. -/
def kernelTensorIsoOverSpec :
    (Scheme.Modules.pullback (extensionHom w a a' π hπ)).obj
      (obstructionSequenceOverSpec w F a a' π hπ).X₁ ≅
    tensorObj (modulePullback w F (Over.mk a))
      ((Scheme.Modules.pullback (extensionHom w a a' π hπ)).obj (baseKernelSheaf w a' π)) :=
  Scheme.Modules.pullbackTensorIso (extensionHom w a a' π hπ)
      (baseKernelSheaf w a' π) (modulePullback w F (Over.mk a')) ≪≫
    tensorIso (Iso.refl _) (moduleIsoOverSpec w F a a' π hπ).symm ≪≫ (β_ _ _).symm

/-- The forward change-of-rings comparison for the pulled base-kernel sheaf. -/
def conormalToTildeOverSpec :
    (Scheme.Modules.pullback (extensionHom w a a' π hπ)).obj (baseKernelSheaf w a' π) ⟶
    (Scheme.Modules.pullback (baseChangeFst w (Over.mk a))).obj
      ((tilde.functor (CommRingCat.of A)).obj (kernelOverSpec π)) :=
  (Scheme.Modules.pullbackComp (extensionHom w a a' π hπ)
      (baseChangeFst w (Over.mk a'))).hom.app _ ≫
    (Scheme.Modules.pullbackCongr (baseChangeMap_fst w (extensionOverMap a a' π hπ))).hom.app _ ≫
    (Scheme.Modules.pullbackComp (baseChangeFst w (Over.mk a))
      (Spec.map (CommRingCat.ofHom π))).inv.app _ ≫
    (Scheme.Modules.pullback (baseChangeFst w (Over.mk a))).map
      ((tilde.ChangeOfRings.Pullback.iso (CommRingCat.ofHom π)).hom.app
        ((ModuleCat.restrictScalars π).obj (kernelOverSpec π))) ≫
    (Scheme.Modules.pullback (baseChangeFst w (Over.mk a))).map
      ((tilde.functor (CommRingCat.of A)).map
        ((ModuleCat.extendRestrictScalarsAdj π).counit.app (kernelOverSpec π)))

/-- The comparison of the pulled kernel tensor with the prescribed tensor sheaf. -/
def obstructionKernelComparisonOverSpec :
    (Scheme.Modules.pullback (extensionHom w a a' π hπ)).obj
      (obstructionSequenceOverSpec w F a a' π hπ).X₁ ⟶
    tensorOverSpec w F a (kernelOverSpec π) :=
  (kernelTensorIsoOverSpec w F a a' π hπ).hom ≫
    tensorHom (𝟙 (modulePullback w F (Over.mk a))) (conormalToTildeOverSpec w a a' π hπ)

/-- The forward kernel comparison is an isomorphism for a square-zero surjection. -/
instance obstructionKernelComparisonOverSpec_isIso :
    IsIso (obstructionKernelComparisonOverSpec w F a a' π hπ) := sorry

/-- A section transported into the last term of the base-kernel tensor sequence. -/
def sequenceSectionOverSpec (x : Γ(modulePullback w F (Over.mk a), ⊤)) :
    Γ((obstructionSequenceOverSpec w F a a' π hπ).X₃, ⊤) :=
  Scheme.Modules.globalSectionsMap (moduleIsoOverSpec w F a a' π hπ).hom x

/-- The Ext connecting image of a section in the base-kernel tensor sequence. -/
def connectingClassOverSpec
    (hS : (obstructionSequenceOverSpec w F a a' π hπ).ShortExact)
    (x : Γ(modulePullback w F (Over.mk a), ⊤)) :
    Scheme.Hom.cohomology (baseChangeFst w (Over.mk a'))
      (obstructionSequenceOverSpec w F a a' π hπ).X₁ 1 :=
  Scheme.Hom.cohomologyBoundaryFromExt (baseChangeFst w (Over.mk a')) hS
    (sequenceSectionOverSpec w F a a' π hπ x)

/-- The adjunction unit on the base-kernel tensor term. -/
def obstructionSequenceOverSpecUnit :
    (obstructionSequenceOverSpec w F a a' π hπ).X₁ ⟶
    (Scheme.Modules.pushforward (extensionHom w a a' π hπ)).obj
      ((Scheme.Modules.pullback (extensionHom w a a' π hπ)).obj
        (obstructionSequenceOverSpec w F a a' π hπ).X₁) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (extensionHom w a a' π hπ)).unit.app _

/-- The base-kernel tensor term is already supported on the closed test scheme. -/
instance obstructionSequenceOverSpecUnit_isIso :
    IsIso (obstructionSequenceOverSpecUnit w F a a' π hπ) := sorry

end Extension

/-- The forward map on cohomology induced by a module map into a direct image. -/
private def cohomologyForward {X Y : Scheme.{u}} {R B : Type u} [CommRing R] [CommRing B]
    (a : Y ⟶ Spec (CommRingCat.of R)) (b : X ⟶ Spec (CommRingCat.of B))
    (f : X ⟶ Y) {G : Y.Modules} {H : X.Modules}
    (φ : G ⟶ (Scheme.Modules.pushforward f).obj H) (p : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj (Scheme.Hom.cohomology a G p) ⟶
      (forget₂ (ModuleCat B) AddCommGrpCat).obj (Scheme.Hom.cohomology b H p) :=
  eqToHom (Scheme.Hom.cohomologyForget_obj_eq a G p) ≫
    CategoryTheory.Sheaf.cohomologyMap ((SheafOfModules.toSheaf Y.ringCatSheaf).map φ) p ⊤ ≫
    CategoryTheory.Sheaf.pushforwardCohomologyMap f.base
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj H) p ⊤ ≫
    eqToHom (Scheme.Hom.cohomologyForget_obj_eq b H p).symm

section Extension

variable {A A' : Type u} [CommRing A] [CommRing A']
variable (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of Λ))
variable (a' : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of Λ))
variable (π : A' →+* A) [π.IsSquareZeroExtension]
variable (hπ : Spec.map (CommRingCat.ofHom π) ≫ a' = a)

/-- Forward transport of the connecting class to the pulled base-kernel tensor. -/
def connectingPullbackOverSpec
    (y : Scheme.Hom.cohomology (baseChangeFst w (Over.mk a'))
      (obstructionSequenceOverSpec w F a a' π hπ).X₁ 1) :
    Scheme.Hom.cohomology (baseChangeFst w (Over.mk a))
      ((Scheme.Modules.pullback (extensionHom w a a' π hπ)).obj
        (obstructionSequenceOverSpec w F a a' π hπ).X₁) 1 :=
  cohomologyForward (baseChangeFst w (Over.mk a')) (baseChangeFst w (Over.mk a))
    (extensionHom w a a' π hπ) (obstructionSequenceOverSpecUnit w F a a' π hπ) 1 y

/-- The canonical boundary obstruction for a section over an explicit affine test scheme. -/
def obstructionClassOverSpec (hflat : Scheme.Modules.flatOver F w)
    (x : Γ(modulePullback w F (Over.mk a), ⊤)) :
    (obstructionModuleOverSpec w F a).obj (kernelOverSpec π) :=
  ((Scheme.Hom.cohomologyFunctor (baseChangeFst w (Over.mk a)) 1).map
    (obstructionKernelComparisonOverSpec w F a a' π hπ))
      (connectingPullbackOverSpec w F a a' π hπ
        (connectingClassOverSpec w F a a' π hπ
          (obstructionSequenceOverSpec_shortExact w F a a' π hπ hflat) x))

/-- A section lifts across a compatible square-zero extension exactly when its boundary obstruction vanishes. -/
theorem exists_lift_iff_obstructionClassOverSpec_eq_zero
    [SheafOfModules.IsQuasicoherent F] (hflat : Scheme.Modules.flatOver F w)
    (x : Γ(modulePullback w F (Over.mk a), ⊤)) :
    (∃ y : Γ(modulePullback w F (Over.mk a'), ⊤),
      sectionsRestrict w F (extensionOverMap a a' π hπ) y = x) ↔
        obstructionClassOverSpec w F a a' π hπ hflat x = 0 := sorry

end Extension

/-- The sheaf `F_A ⊗_A M` on `W_A`, obtained by pulling `M^~` back from `Spec(A)` and tensoring
with `F_A`. -/
def tensorModule (A : Type u) [CommRing A] [Algebra Λ A] (M : ModuleCat A) :
    (affineBaseChange w A).Modules :=
  tensorOverSpec w F (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) M

/-- `tensorModule` is the tensor of `F_A` with the pullback of `M^~`. -/
theorem tensorModule_obj (A : Type u) [CommRing A] [Algebra Λ A] (M : ModuleCat A) :
    tensorModule w F A M =
      tensorObj (affineModulePullback w F A)
        ((Scheme.Modules.pullback (baseChangeFst w (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A))))).obj
          ((tilde.functor (CommRingCat.of A)).obj M)) :=
  rfl

/-- A morphism of `A`-modules induces a morphism of the associated tensor sheaves on `W_A`. -/
def tensorModuleMap (A : Type u) [CommRing A] [Algebra Λ A] {M N : ModuleCat A} (f : M ⟶ N) :
    tensorModule w F A M ⟶ tensorModule w F A N :=
  tensorOverSpecMap w F (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) f

/-- Degree-`p` cohomology of modules on `W_A`, as `A`-modules via `W_A ⟶ Spec(A)`. -/
abbrev cohomologyMod (A : Type u) [CommRing A] [Algebra Λ A] (p : ℕ) :
    (affineBaseChange w A).Modules ⥤ ModuleCat A :=
  Scheme.Hom.cohomologyFunctor (baseChangeFst w (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A)))) p

/-- The obstruction functor `O_x`, sending `M` to `H^1(W_A, F_A ⊗_A M)`. The section `x` is
not used in the formula. -/
def obstructionModule (A : Type u) [CommRing A] [Algebra Λ A] :
    ModuleCat A ⥤ ModuleCat A :=
  obstructionModuleOverSpec w F (Spec.map (CommRingCat.ofHom (algebraMap Λ A)))

/-- Evaluating the obstruction functor on `M` recovers `H^1(W_A, F_A ⊗_A M)`. -/
theorem obstructionModule_obj (A : Type u) [CommRing A] [Algebra Λ A] (M : ModuleCat A) :
    (obstructionModule w F A).obj M = (cohomologyMod w A 1).obj (tensorModule w F A M) :=
  rfl

/-- The kernel `I = Ker(A' → A)` as an object of `ModuleCat A`. -/
abbrev kernelModule (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A' A]
    [(algebraMap A' A).IsSquareZeroExtension] : ModuleCat A :=
  ModuleCat.of A (RingHom.ker (algebraMap A' A))

/-- `kernelModule` is the kernel of `algebraMap A' A`, as an `A`-module. -/
theorem kernelModule_obj (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    kernelModule A A' = ModuleCat.of A (RingHom.ker (algebraMap A' A)) :=
  rfl

/-- The canonical short exact sequence of the thickening `W_A ⟶ W_{A'}`, as a complex on
`W_{A'}`. -/
def obstructionSequence (A A' : Type u) [CommRing A] [CommRing A'] [Algebra Λ A] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A] [(algebraMap A' A).IsSquareZeroExtension] :
    ShortComplex (affineBaseChange w A').Modules :=
  obstructionSequenceOverSpec w F (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) (Spec.map (CommRingCat.ofHom (algebraMap Λ A'))) (algebraMap A' A) (specOverMap_w Λ A A')

/-- Flatness of `F` over `S` makes the unpulled obstruction sequence short exact. -/
theorem obstructionSequence_shortExact (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (hflat : Scheme.Modules.flatOver F w) :
    (obstructionSequence w F A A').ShortExact :=
  obstructionSequenceOverSpec_shortExact w F (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) (Spec.map (CommRingCat.ofHom (algebraMap Λ A'))) (algebraMap A' A) (specOverMap_w Λ A A') hflat

/-- The comparison identifying `F_A` with `i^* F_{A'}` along `W_A ⟶ W_{A'}`. -/
def affineModuleIso (A A' : Type u) [CommRing A] [CommRing A'] [Algebra Λ A] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A] :
    affineModulePullback w F A ≅
      (Scheme.Modules.pullback (thickeningHom w A A')).obj (affineModulePullback w F A') :=
  moduleIsoOverSpec w F (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) (Spec.map (CommRingCat.ofHom (algebraMap Λ A'))) (algebraMap A' A) (specOverMap_w Λ A A')

/-- `affineModuleIso` is the pullback-composition comparison of `F_A` with `i^* F_{A'}`. -/
theorem affineModuleIso_hom (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A] :
    (affineModuleIso w F A A').hom = modulePullbackMap w F (specOverMap Λ A A') :=
  moduleIsoOverSpec_hom w F (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) (Spec.map (CommRingCat.ofHom (algebraMap Λ A'))) (algebraMap A' A) (specOverMap_w Λ A A')

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
    Scheme.Modules.globalSectionsMap (affineModuleIso w F A A').hom x

/-- `toObstructionSequenceX3` applies the identification `F_A ≅ i^* F_{A'}` on global sections. -/
theorem toObstructionSequenceX3_eq (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (x : Γ(affineModulePullback w F A, ⊤)) :
    toObstructionSequenceX3 w F A A' x =
      (obstructionSequence_x3_sections w F A A').symm ▸
        Scheme.Modules.globalSectionsMap (affineModuleIso w F A A').hom x :=
  rfl

/-- Pullback identifies the base-kernel tensor term with the tensor of the closed module and pulled kernel. -/
def obstructionKernelTensorIso (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    (Scheme.Modules.pullback (thickeningHom w A A')).obj (obstructionSequence w F A A').X₁ ≅
      tensorObj (affineModulePullback w F A)
        ((Scheme.Modules.pullback (thickeningHom w A A')).obj
          (baseKernelSheaf w (Spec.map (CommRingCat.ofHom (algebraMap Λ A'))) (algebraMap A' A))) :=
  kernelTensorIsoOverSpec w F (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) (Spec.map (CommRingCat.ofHom (algebraMap Λ A'))) (algebraMap A' A) (specOverMap_w Λ A A')

/-- The forward affine change-of-rings map for the pulled base-kernel sheaf. -/
def obstructionConormalToTilde (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    (Scheme.Modules.pullback (thickeningHom w A A')).obj
      (baseKernelSheaf w (Spec.map (CommRingCat.ofHom (algebraMap Λ A'))) (algebraMap A' A)) ⟶
    (Scheme.Modules.pullback (baseChangeFst w
      (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A))))).obj
        ((tilde.functor (CommRingCat.of A)).obj (kernelModule A A')) :=
  conormalToTildeOverSpec w (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) (Spec.map (CommRingCat.ofHom (algebraMap Λ A'))) (algebraMap A' A) (specOverMap_w Λ A A')

/-- The comparison morphism from `i^*(K ⊗ F_{A'})` to `F_A ⊗_A I^~`. -/
def obstructionKernelComparison (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    (Scheme.Modules.pullback (thickeningHom w A A')).obj (obstructionSequence w F A A').X₁ ⟶
      tensorModule w F A (kernelModule A A') :=
  obstructionKernelComparisonOverSpec w F (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) (Spec.map (CommRingCat.ofHom (algebraMap Λ A'))) (algebraMap A' A) (specOverMap_w Λ A A')

/-- `obstructionKernelComparison` is the tensor of `F_A` with the tilde comparison of the
pulled base kernel. -/
theorem obstructionKernelComparison_eq (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension] :
    obstructionKernelComparison w F A A' =
      (obstructionKernelTensorIso w F A A').hom ≫
        tensorHom (𝟙 (affineModulePullback w F A)) (obstructionConormalToTilde w A A') :=
  rfl

/-- The connecting image of `x` in `H^1(W_{A'}, K ⊗ F_{A'})`. -/
def obstructionConnectingClass (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (hS : (obstructionSequence w F A A').ShortExact)
    (x : Γ(affineModulePullback w F A, ⊤)) :
    Scheme.Hom.cohomology (baseChangeFst w (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A'))))
      (obstructionSequence w F A A').X₁ 1 :=
  Scheme.Hom.cohomologyBoundaryFromExt (baseChangeFst w (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A')))) hS
    (toObstructionSequenceX3 w F A A' x)

/-- Direct-image cohomology of a module on `W_A`, as an additive sheaf on `W_{A'}`. -/
private def obstructionPushforwardToSheaf (A A' : Type u) [CommRing A] [CommRing A']
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
  obstructionSequenceOverSpecUnit w F (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) (Spec.map (CommRingCat.ofHom (algebraMap Λ A'))) (algebraMap A' A) (specOverMap_w Λ A A')

/-- Pullback of the connecting class along `W_A ⟶ W_{A'}` into `H^1(W_A, i^*(K ⊗ F_{A'}))`,
by cohomology of the adjunction unit followed by the canonical direct-image comparison. -/
def obstructionConnectingPullback (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (y : Scheme.Hom.cohomology (baseChangeFst w (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A'))))
      (obstructionSequence w F A A').X₁ 1) :
    Scheme.Hom.cohomology (baseChangeFst w (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A))))
      ((Scheme.Modules.pullback (thickeningHom w A A')).obj
        (obstructionSequence w F A A').X₁) 1 :=
  connectingPullbackOverSpec w F (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) (Spec.map (CommRingCat.ofHom (algebraMap Λ A'))) (algebraMap A' A) (specOverMap_w Λ A A') y

/-- The obstruction class of a global section `x` of `F_A` along a square-zero extension
`A' → A`, as an element of `O_x(I) = H^1(W_A, F_A ⊗_A I)`. -/
def obstructionClass (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (hflat : Scheme.Modules.flatOver F w)
    (x : Γ(affineModulePullback w F A, ⊤)) :
    (obstructionModule w F A).obj (kernelModule A A') :=
  obstructionClassOverSpec w F (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) (Spec.map (CommRingCat.ofHom (algebraMap Λ A'))) (algebraMap A' A) (specOverMap_w Λ A A') hflat x

/-- The obstruction class is the image of `x` under `cohomologyBoundaryFromExt` on `W_{A'}`,
transported by cohomology of the adjunction unit, the direct-image comparison, and the
comparison `i^*(K ⊗ F_{A'}) ⟶ F_A ⊗_A I^~`. -/
theorem obstructionClass_spec (A A' : Type u) [CommRing A] [CommRing A']
    [Algebra Λ A] [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
    [(algebraMap A' A).IsSquareZeroExtension]
    (hflat : Scheme.Modules.flatOver F w)
    (x : Γ(affineModulePullback w F A, ⊤)) :
    obstructionClass w F A A' hflat x =
      ((cohomologyMod w A 1).map (obstructionKernelComparison w F A A')).hom
        (obstructionConnectingPullback w F A A'
          (Scheme.Hom.cohomologyBoundaryFromExt (baseChangeFst w (Scheme.OverSpec.affine (CommRingCat.ofHom (algebraMap Λ A'))))
            (obstructionSequence_shortExact w F A A' hflat)
            (toObstructionSequenceX3 w F A A' x))) :=
  rfl

/-- The obstruction-module functor associated to an object of the sections fibration. -/
def obstructionModuleAt (ξ : ObjectOverSpec (toGroupoids w F)) :
    ModuleCat ξ.carrier ⥤ ModuleCat ξ.carrier :=
  obstructionModuleOverSpec w F ξ.toS

/-- A map of obstruction triples induces the canonical map of tensor sheaves after pullback. -/
private def tensorTripleMap {ξ η : ObstructionTriple (toGroupoids w F)}
    (f : ObstructionTriple.Hom ξ η) :
    (Scheme.Modules.pullback (baseChangeMap w f.toHom.overMap)).obj
      (tensorOverSpec w F ξ.toS ξ.M) ⟶ tensorOverSpec w F η.toS η.M :=
  (Scheme.Modules.pullbackTensorIso (baseChangeMap w f.toHom.overMap)
    (modulePullback w F (Over.mk ξ.toS))
    ((Scheme.Modules.pullback (baseChangeFst w (Over.mk ξ.toS))).obj
      ((tilde.functor ξ.toCommRingCat).obj ξ.M))).hom ≫
    tensorHom
      ((Scheme.Modules.pullbackComp (baseChangeMap w f.toHom.overMap)
          (baseChangeSnd w (Over.mk ξ.toS))).hom.app F ≫
        (Scheme.Modules.pullbackCongr (baseChangeMap_snd w f.toHom.overMap)).hom.app F)
      ((Scheme.Modules.pullbackComp (baseChangeMap w f.toHom.overMap)
          (baseChangeFst w (Over.mk ξ.toS))).hom.app _ ≫
        (Scheme.Modules.pullbackCongr (baseChangeMap_fst w f.toHom.overMap)).hom.app _ ≫
        (Scheme.Modules.pullbackComp (baseChangeFst w (Over.mk η.toS))
          (Spec.map (CommRingCat.ofHom f.toRingHom))).inv.app _ ≫
        (Scheme.Modules.pullback (baseChangeFst w (Over.mk η.toS))).map
          ((tilde.ChangeOfRings.Pullback.iso (CommRingCat.ofHom f.toRingHom)).hom.app ξ.M) ≫
        (Scheme.Modules.pullback (baseChangeFst w (Over.mk η.toS))).map
          ((tilde.functor η.toCommRingCat).map
            ((ModuleCat.extendRestrictScalarsAdj f.toRingHom).homEquiv ξ.M η.M |>.symm f.toModule)))

/-- The additive cohomology map induced by a morphism of obstruction triples. -/
def obstructionMapAdd {ξ η : ObstructionTriple (toGroupoids w F)}
    (f : ObstructionTriple.Hom ξ η) :
    (forget₂ (ModuleCat ξ.carrier) AddCommGrpCat).obj ((obstructionModuleAt w F ξ.toObjectOverSpec).obj ξ.M) ⟶
      (forget₂ (ModuleCat ξ.carrier) AddCommGrpCat).obj
        ((ModuleCat.restrictScalars f.toRingHom).obj
          ((obstructionModuleAt w F η.toObjectOverSpec).obj η.M)) :=
  cohomologyForward (baseChangeFst w (Over.mk ξ.toS)) (baseChangeFst w (Over.mk η.toS))
    (baseChangeMap w f.toHom.overMap)
    ((Scheme.Modules.pullbackPushforwardAdjunction (baseChangeMap w f.toHom.overMap)).homEquiv _ _
      (tensorTripleMap w F f)) 1

/-- The cohomology map of a morphism of triples respects the restricted scalar action. -/
theorem obstructionMap_smul {ξ η : ObstructionTriple (toGroupoids w F)}
    (f : ObstructionTriple.Hom ξ η) (r : ξ.carrier) :
    obstructionMapAdd w F f ≫
      ((ModuleCat.restrictScalars f.toRingHom).obj
        ((obstructionModuleAt w F η.toObjectOverSpec).obj η.M)).smul r =
      ((obstructionModuleAt w F ξ.toObjectOverSpec).obj ξ.M).smul r ≫ obstructionMapAdd w F f := sorry

/-- The scalar-compatible obstruction map of a morphism of triples. -/
def obstructionMap {ξ η : ObstructionTriple (toGroupoids w F)}
    (f : ObstructionTriple.Hom ξ η) :
    (obstructionModuleAt w F ξ.toObjectOverSpec).obj ξ.M ⟶
      (ModuleCat.restrictScalars f.toRingHom).obj
        ((obstructionModuleAt w F η.toObjectOverSpec).obj η.M) :=
  ModuleCat.homMk (obstructionMapAdd w F f) (obstructionMap_smul w F f)

/-- Identity morphisms of triples induce the identity obstruction map with restricted scalars. -/
theorem obstructionMap_id (ξ : ObstructionTriple (toGroupoids w F)) :
    obstructionMap w F (ObstructionTriple.Hom.id ξ) =
      (ModuleCat.restrictScalarsId ξ.carrier).inv.app
        ((obstructionModuleAt w F ξ.toObjectOverSpec).obj ξ.M) := sorry

/-- Obstruction maps respect composition and the canonical restriction-of-scalars comparison. -/
theorem obstructionMap_comp {ξ η ζ : ObstructionTriple (toGroupoids w F)}
    (f : ObstructionTriple.Hom ξ η) (g : ObstructionTriple.Hom η ζ) :
    obstructionMap w F (ObstructionTriple.Hom.comp f g) =
      obstructionMap w F f ≫ (ModuleCat.restrictScalars f.toRingHom).map (obstructionMap w F g) ≫
        (ModuleCat.restrictScalarsComp' f.toRingHom g.toRingHom
          (g.toRingHom.comp f.toRingHom) rfl).inv.app
            ((obstructionModuleAt w F ζ.toObjectOverSpec).obj ζ.M) := sorry

/-- Obstruction maps over a fixed affine object agree with the module functor. -/
theorem obstructionMap_module (ξ : ObjectOverSpec (toGroupoids w F))
    {M N : ModuleCat ξ.carrier} (f : M ⟶ N) :
    obstructionMap w F (ObstructionTriple.Hom.ofModuleHom ξ f) =
      (obstructionModuleAt w F ξ).map f ≫ (ModuleCat.restrictScalarsId ξ.carrier).inv.app
        ((obstructionModuleAt w F ξ).obj N) := sorry

/-- The boundary class of a deformation situation for the global-sections fibration. -/
def obstructionClassAt (hflat : Scheme.Modules.flatOver F w)
    (σ : DeformationSituation (toGroupoids w F)) :
    (obstructionModuleAt w F σ.toObjectOverSpec).obj σ.kernelModule :=
  obstructionClassOverSpec w F σ.toS σ.sourceToS σ.extension.hom σ.toS_comp hflat
    (sectionAt w F σ.toObjectOverSpec)

/-- Boundary obstruction classes are natural under morphisms of deformation situations. -/
theorem obstructionClassAt_naturality (hflat : Scheme.Modules.flatOver F w)
    {σ τ : DeformationSituation (toGroupoids w F)} (f : DeformationSituation.Hom σ τ) :
    obstructionMap w F f.toTripleHom (obstructionClassAt w F hflat σ) =
      obstructionClassAt w F hflat τ := sorry

/-- Lifts of an affine fiber object exist exactly when its canonical obstruction vanishes. -/
theorem obstructionClassAt_lifts_iff [SheafOfModules.IsQuasicoherent F]
    (hflat : Scheme.Modules.flatOver F w) (σ : DeformationSituation (toGroupoids w F)) :
    Nonempty (DeformationSituation.ObjectLift σ) ↔ obstructionClassAt w F hflat σ = 0 := sorry

/-- The obstruction theory of sections of a quasi-coherent module flat over a Noetherian affine base. -/
def obstructionTheory [SheafOfModules.IsQuasicoherent F] (hflat : Scheme.Modules.flatOver F w) :
    ObstructionTheory (toGroupoids w F) where
  module := obstructionModuleAt w F
  moduleLinear ξ := obstructionModuleOverSpec_moduleLinear w F ξ.toS
  map := obstructionMap w F
  obstruction := obstructionClassAt w F hflat
  map_id := obstructionMap_id w F
  map_comp := obstructionMap_comp w F
  map_module := obstructionMap_module w F
  map_obstruction := obstructionClassAt_naturality w F hflat
  lifts_iff := obstructionClassAt_lifts_iff w F hflat

/-- The obstruction theory uses first cohomology of the pulled module tensored with the test module. -/
theorem obstructionTheory_module [SheafOfModules.IsQuasicoherent F]
    (hflat : Scheme.Modules.flatOver F w) (ξ : ObjectOverSpec (toGroupoids w F)) (M : ModuleCat ξ.carrier) :
    ((obstructionTheory w F hflat).module ξ).obj M =
      Scheme.Hom.cohomology (baseChangeFst w (Over.mk ξ.toS)) (tensorOverSpec w F ξ.toS M) 1 := rfl

/-- The obstruction theory uses the canonical boundary class of the stored section. -/
theorem obstructionTheory_obstruction [SheafOfModules.IsQuasicoherent F]
    (hflat : Scheme.Modules.flatOver F w) (σ : DeformationSituation (toGroupoids w F)) :
    (obstructionTheory w F hflat).obstruction σ =
      obstructionClassOverSpec w F σ.toS σ.sourceToS σ.extension.hom σ.toS_comp hflat
        (sectionAt w F σ.toObjectOverSpec) := rfl

/-- An affine section lifts through a square-zero extension exactly when its boundary class vanishes. -/
theorem exists_lift_iff_obstructionClass_eq_zero [SheafOfModules.IsQuasicoherent F]
    (hflat : Scheme.Modules.flatOver F w)
    {A A' : Type u} [CommRing A] [CommRing A'] [Algebra Λ A] [Algebra Λ A']
    [Algebra A' A] [IsScalarTower Λ A' A] [(algebraMap A' A).IsSquareZeroExtension]
    (x : Γ(affineModulePullback w F A, ⊤)) :
    (∃ y : Γ(affineModulePullback w F A', ⊤),
      (sectionsFunctor w F).map (specOverMap Λ A A').op y = x) ↔
      obstructionClass w F A A' hflat x = 0 :=
  exists_lift_iff_obstructionClassOverSpec_eq_zero w F
    (Spec.map (CommRingCat.ofHom (algebraMap Λ A)))
    (Spec.map (CommRingCat.ofHom (algebraMap Λ A')))
    (algebraMap A' A) (specOverMap_w Λ A A') hflat x

end AlgebraicGeometry.GroupoidsOver.GlobalSections
