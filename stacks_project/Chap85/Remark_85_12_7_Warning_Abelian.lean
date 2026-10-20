/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import stacks_project.Chap85.Lemma_85_11_1_Flat
public import stacks_project.Chap85.Lemma_85_12_5_Equivalence

/-!
# Abelian structure on cartesian modules from two flat 1-cofaces

If only `f_{δ 1}` and `f_{δ 0}` are flat, kernels and cokernels of cartesian
`O`-modules are computed on face-descent data from kernels in `Mod(O_0)` and
the kernel comparison of the two exact pullbacks, then transported along
`cartesianEquivalence`. This does not make cartesian modules a Serre
subcategory of `Mod(O)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites.Module

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instMorphismDiagram : IsMorphismDiagram C J]
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w,
    (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived (stageMorphism C J O n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]
include instMorphismDiagram instWeakSheafify instLeftKan

/-- Module pullback along a 1-coface `f_{δ i} : (Sh(C_1), O_1) ⟶ (Sh(C_0), O_0)`. -/
abbrev cofacePullback (i : Fin 2) :
    SheafOfModules.{w} (componentRingedSite C J O ⦋0⦌).structureSheaf ⥤
      SheafOfModules.{w} (componentRingedSite C J O ⦋1⦌).structureSheaf :=
  (ringedToposMap C J O (SimplexCategory.δ i)).modulePullback

/-- `cofacePullback i` is module pullback along `ringedToposMap` of `δ i`. -/
theorem cofacePullback_eq (i : Fin 2) :
    cofacePullback C J O i =
      (ringedToposMap C J O (SimplexCategory.δ i)).modulePullback :=
  sorry

namespace FaceDescent

variable {C J O}

/-- Hom-groups of face-descent pairs, with operations on the underlying `O_0`-module maps. -/
@[reducible]
def homAddCommGroup (D E : FaceDescent C J O) : AddCommGroup (D ⟶ E) :=
  let zero : Zero (D ⟶ E) := ⟨homMk (0 : D.module ⟶ E.module) sorry⟩
  let add : Add (D ⟶ E) := ⟨fun f g ↦ homMk (f.hom + g.hom) sorry⟩
  let neg : Neg (D ⟶ E) := ⟨fun f ↦ homMk (-f.hom) sorry⟩
  let sub : Sub (D ⟶ E) := ⟨fun f g ↦ homMk (f.hom - g.hom) sorry⟩
  let nsmul : SMul ℕ (D ⟶ E) := ⟨fun n f ↦ homMk (n • f.hom) sorry⟩
  let zsmul : SMul ℤ (D ⟶ E) := ⟨fun n f ↦ homMk (n • f.hom) sorry⟩
  @Function.Injective.addCommGroup (D ⟶ E) (D.module ⟶ E.module)
    add zero nsmul neg sub zsmul inferInstance (fun f ↦ f.hom) sorry rfl
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Addition of face-descent morphisms is addition of the underlying `O_0`-module maps. -/
theorem homAddCommGroup_add_hom {D E : FaceDescent C J O} (f g : D ⟶ E) :
    ((homAddCommGroup D E).add f g).hom = f.hom + g.hom :=
  sorry

end FaceDescent

/-- Face-descent pairs form a preadditive category via their underlying `O_0`-module maps. -/
instance instPreadditiveFaceDescent : Preadditive (FaceDescent C J O) where
  homGroup D E := FaceDescent.homAddCommGroup D E
  add_comp := sorry
  comp_add := sorry

/-- Finite products of cartesian `O`-modules remain cartesian, with no flatness hypothesis. -/
instance instHasFiniteProductsCartesian : HasFiniteProducts (Cartesian C J O) :=
  sorry

variable [ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2)))]
variable [ToposHom.IsFlat (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2)))]
variable [HasSheafify ((J ⦋0⦌).toGrothendieck) AddCommGrpCat.{w}]
variable [((J ⦋0⦌).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Pullback along `f_{δ 0}` preserves finite limits. -/
instance preservesFiniteLimits_cofacePullback0 :
    PreservesFiniteLimits (cofacePullback C J O (0 : Fin 2)) :=
  (ToposHom.IsFlat.exactPullback
    (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2)))).property.1

/-- Pullback along `f_{δ 1}` preserves finite limits. -/
instance preservesFiniteLimits_cofacePullback1 :
    PreservesFiniteLimits (cofacePullback C J O (1 : Fin 2)) :=
  (ToposHom.IsFlat.exactPullback
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2)))).property.1

/-- Pullback along `f_{δ 0}` preserves finite colimits. -/
instance preservesFiniteColimits_cofacePullback0 :
    PreservesFiniteColimits (cofacePullback C J O (0 : Fin 2)) :=
  (ToposHom.IsFlat.exactPullback
    (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2)))).property.2

/-- Pullback along `f_{δ 1}` preserves finite colimits. -/
instance preservesFiniteColimits_cofacePullback1 :
    PreservesFiniteColimits (cofacePullback C J O (1 : Fin 2)) :=
  (ToposHom.IsFlat.exactPullback
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2)))).property.2

namespace FaceDescent

variable {C J O}

/-- The coface isomorphism on the kernel of an `O_0`-module map, via kernel comparison of the
two exact 1-coface pullbacks. -/
def kernelIso {D E : FaceDescent C J O} (f : D ⟶ E) :
    (cofacePullback C J O (1 : Fin 2)).obj (Limits.kernel f.hom) ≅
      (cofacePullback C J O (0 : Fin 2)).obj (Limits.kernel f.hom) :=
  PreservesKernel.iso (cofacePullback C J O (1 : Fin 2)) f.hom ≪≫
    kernel.mapIso ((cofacePullback C J O (1 : Fin 2)).map f.hom)
      ((cofacePullback C J O (0 : Fin 2)).map f.hom) D.iso E.iso f.comm ≪≫
    (PreservesKernel.iso (cofacePullback C J O (0 : Fin 2)) f.hom).symm

/-- The kernel of a morphism of face-descent pairs, with underlying module `kernel f.hom`. -/
def kernel {D E : FaceDescent C J O} (f : D ⟶ E) : FaceDescent C J O :=
  ofIso (Limits.kernel f.hom) (kernelIso f) sorry

/-- The underlying `O_0`-module of `kernel f` is `kernel f.hom`. -/
theorem kernel_module {D E : FaceDescent C J O} (f : D ⟶ E) :
    (kernel f).module = Limits.kernel f.hom :=
  sorry

/-- The kernel inclusion of a morphism of face-descent pairs. -/
def kernelι {D E : FaceDescent C J O} (f : D ⟶ E) : kernel f ⟶ D :=
  homMk (Limits.kernel.ι f.hom) sorry

/-- The underlying map of `kernelι f` is `kernel.ι f.hom`. -/
theorem kernelι_hom {D E : FaceDescent C J O} (f : D ⟶ E) :
    (kernelι f).hom = Limits.kernel.ι f.hom :=
  sorry

/-- The kernel inclusion composes to zero with the original morphism. -/
theorem kernelι_comp {D E : FaceDescent C J O} (f : D ⟶ E) : kernelι f ≫ f = 0 :=
  sorry

/-- An underlying composite that is zero remains zero on `O_0`-modules. -/
theorem hom_comp_eq_zero {W D E : FaceDescent C J O} {f : D ⟶ E} {k : W ⟶ D}
    (h : k ≫ f = 0) : k.hom ≫ f.hom = 0 :=
  sorry

/-- The universal map into the kernel of a morphism of face-descent pairs. -/
def kernelLift {W D E : FaceDescent C J O} (f : D ⟶ E) (k : W ⟶ D) (h : k ≫ f = 0) :
    W ⟶ kernel f :=
  homMk (Limits.kernel.lift f.hom k.hom (hom_comp_eq_zero h)) sorry

/-- The underlying map of `kernelLift` is `kernel.lift` of the underlying maps. -/
theorem kernelLift_hom {W D E : FaceDescent C J O} (f : D ⟶ E) (k : W ⟶ D)
    (h : k ≫ f = 0) :
    (kernelLift f k h).hom = Limits.kernel.lift f.hom k.hom (hom_comp_eq_zero h) :=
  sorry

/-- The kernel fork of a morphism of face-descent pairs. -/
def kerFork {D E : FaceDescent C J O} (f : D ⟶ E) : KernelFork f :=
  KernelFork.ofι (kernelι f) (kernelι_comp f)

/-- The named kernel fork is a limit cone. -/
def isLimit_kerFork {D E : FaceDescent C J O} (f : D ⟶ E) : IsLimit (kerFork f) where
  lift s := kernelLift f (Fork.ι s) (KernelFork.condition s)
  fac := sorry
  uniq := sorry

/-- The coface isomorphism on the cokernel of an `O_0`-module map, via cokernel comparison of
the two exact 1-coface pullbacks. -/
def cokernelIso {D E : FaceDescent C J O} (f : D ⟶ E) :
    (cofacePullback C J O (1 : Fin 2)).obj (Limits.cokernel f.hom) ≅
      (cofacePullback C J O (0 : Fin 2)).obj (Limits.cokernel f.hom) :=
  PreservesCokernel.iso (cofacePullback C J O (1 : Fin 2)) f.hom ≪≫
    cokernel.mapIso ((cofacePullback C J O (1 : Fin 2)).map f.hom)
      ((cofacePullback C J O (0 : Fin 2)).map f.hom) D.iso E.iso f.comm ≪≫
    (PreservesCokernel.iso (cofacePullback C J O (0 : Fin 2)) f.hom).symm

/-- The cokernel of a morphism of face-descent pairs, with underlying module `cokernel f.hom`. -/
def cokernel {D E : FaceDescent C J O} (f : D ⟶ E) : FaceDescent C J O :=
  ofIso (Limits.cokernel f.hom) (cokernelIso f) sorry

/-- The underlying `O_0`-module of `cokernel f` is `cokernel f.hom`. -/
theorem cokernel_module {D E : FaceDescent C J O} (f : D ⟶ E) :
    (cokernel f).module = Limits.cokernel f.hom :=
  sorry

/-- The cokernel projection of a morphism of face-descent pairs. -/
def cokernelπ {D E : FaceDescent C J O} (f : D ⟶ E) : E ⟶ cokernel f :=
  homMk (Limits.cokernel.π f.hom) sorry

/-- The underlying map of `cokernelπ f` is `cokernel.π f.hom`. -/
theorem cokernelπ_hom {D E : FaceDescent C J O} (f : D ⟶ E) :
    (cokernelπ f).hom = Limits.cokernel.π f.hom :=
  sorry

/-- The original morphism composes to zero with the cokernel projection. -/
theorem cokernelπ_comp {D E : FaceDescent C J O} (f : D ⟶ E) : f ≫ cokernelπ f = 0 :=
  sorry

/-- An underlying composite that is zero remains zero on `O_0`-modules, dual form. -/
theorem hom_comp_eq_zero' {D E T : FaceDescent C J O} {f : D ⟶ E} {g : E ⟶ T}
    (h : f ≫ g = 0) : f.hom ≫ g.hom = 0 :=
  sorry

/-- The universal map out of the cokernel of a morphism of face-descent pairs. -/
def cokernelDesc {D E T : FaceDescent C J O} (f : D ⟶ E) (g : E ⟶ T) (h : f ≫ g = 0) :
    cokernel f ⟶ T :=
  homMk (Limits.cokernel.desc f.hom g.hom (hom_comp_eq_zero' h)) sorry

/-- The underlying map of `cokernelDesc` is `cokernel.desc` of the underlying maps. -/
theorem cokernelDesc_hom {D E T : FaceDescent C J O} (f : D ⟶ E) (g : E ⟶ T)
    (h : f ≫ g = 0) :
    (cokernelDesc f g h).hom = Limits.cokernel.desc f.hom g.hom (hom_comp_eq_zero' h) :=
  sorry

/-- The cokernel cofork of a morphism of face-descent pairs. -/
def cokerCofork {D E : FaceDescent C J O} (f : D ⟶ E) : CokernelCofork f :=
  CokernelCofork.ofπ (cokernelπ f) (cokernelπ_comp f)

/-- The named cokernel cofork is a colimit cocone. -/
def isColimit_cokerCofork {D E : FaceDescent C J O} (f : D ⟶ E) :
    IsColimit (cokerCofork f) where
  desc s := cokernelDesc f (Cofork.π s) (CokernelCofork.condition s)
  fac := sorry
  uniq := sorry

end FaceDescent

/-- Face-descent pairs have kernels, computed in `Mod(O_0)` and reassembled by `kernelIso`. -/
instance instHasKernelsFaceDescent_of_isFlat_delta01 : HasKernels (FaceDescent C J O) where
  has_limit := fun f ↦ HasLimit.mk { cone := FaceDescent.kerFork f, isLimit := FaceDescent.isLimit_kerFork f }

/-- Face-descent pairs have cokernels, computed in `Mod(O_0)` and reassembled by `cokernelIso`. -/
instance instHasCokernelsFaceDescent_of_isFlat_delta01 : HasCokernels (FaceDescent C J O) where
  has_colimit := fun f ↦
    HasColimit.mk { cocone := FaceDescent.cokerCofork f, isColimit := FaceDescent.isColimit_cokerCofork f }

/-- If `f_{δ 0}` and `f_{δ 1}` are flat, the category of face-descent pairs is abelian. -/
instance instAbelianFaceDescent_of_isFlat_delta01 : Abelian (FaceDescent C J O) where
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry

end CategoryTheory.SimplicialSites.Module
