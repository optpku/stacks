/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModuleDescent
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Flat

/-!
# Abelian structure on module face-descent data

When the two degree-one coface pullbacks are exact, face-descent data form an abelian
category. Additive operations, kernels, and cokernels are defined on the underlying
degree-zero modules.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open RingedSite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites.Module

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram.{u, v, w} C J]
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
  rfl

namespace FaceDescent

variable {C J O}

/-- Zero, addition, negation, subtraction, and scalar multiplication preserve coface
compatibility, and the underlying-map function is injective. -/
private theorem homAddCommGroup_laws (D E : FaceDescent C J O) :
    ((cofacePullback C J O (1 : Fin 2)).map (0 : D.module ⟶ E.module) ≫ E.iso.hom =
      D.iso.hom ≫ (cofacePullback C J O (0 : Fin 2)).map (0 : D.module ⟶ E.module)) ∧
    (∀ f g : D ⟶ E, (cofacePullback C J O (1 : Fin 2)).map (Hom.hom f + Hom.hom g) ≫ E.iso.hom =
      D.iso.hom ≫ (cofacePullback C J O (0 : Fin 2)).map (Hom.hom f + Hom.hom g)) ∧
    (∀ f : D ⟶ E, (cofacePullback C J O (1 : Fin 2)).map (-Hom.hom f) ≫ E.iso.hom =
      D.iso.hom ≫ (cofacePullback C J O (0 : Fin 2)).map (-Hom.hom f)) ∧
    (∀ f g : D ⟶ E, (cofacePullback C J O (1 : Fin 2)).map (Hom.hom f - Hom.hom g) ≫ E.iso.hom =
      D.iso.hom ≫ (cofacePullback C J O (0 : Fin 2)).map (Hom.hom f - Hom.hom g)) ∧
    (∀ (n : ℕ) (f : D ⟶ E), (cofacePullback C J O (1 : Fin 2)).map (n • Hom.hom f) ≫ E.iso.hom =
      D.iso.hom ≫ (cofacePullback C J O (0 : Fin 2)).map (n • Hom.hom f)) ∧
    (∀ (n : ℤ) (f : D ⟶ E), (cofacePullback C J O (1 : Fin 2)).map (n • Hom.hom f) ≫ E.iso.hom =
      D.iso.hom ≫ (cofacePullback C J O (0 : Fin 2)).map (n • Hom.hom f)) ∧
    Function.Injective (fun (f : D ⟶ E) ↦ Hom.hom f) :=
  sorry

/-- Hom-groups of face-descent pairs, with operations on the underlying `O_0`-module maps. -/
@[reducible]
def homAddCommGroup (D E : FaceDescent C J O) : AddCommGroup (D ⟶ E) :=
  let zero : Zero (D ⟶ E) := ⟨homMk (0 : D.module ⟶ E.module) ((homAddCommGroup_laws D E).1)⟩
  let add : Add (D ⟶ E) := ⟨fun f g ↦ homMk ((Hom.hom f) + (Hom.hom g)) ((homAddCommGroup_laws D E).2.1 f g)⟩
  let neg : Neg (D ⟶ E) := ⟨fun f ↦ homMk (-(Hom.hom f)) ((homAddCommGroup_laws D E).2.2.1 f)⟩
  let sub : Sub (D ⟶ E) := ⟨fun f g ↦ homMk ((Hom.hom f) - (Hom.hom g)) ((homAddCommGroup_laws D E).2.2.2.1 f g)⟩
  let nsmul : SMul ℕ (D ⟶ E) := ⟨fun n f ↦ homMk (n • (Hom.hom f)) ((homAddCommGroup_laws D E).2.2.2.2.1 n f)⟩
  let zsmul : SMul ℤ (D ⟶ E) := ⟨fun n f ↦ homMk (n • (Hom.hom f)) ((homAddCommGroup_laws D E).2.2.2.2.2.1 n f)⟩
  @Function.Injective.addCommGroup (D ⟶ E) (D.module ⟶ E.module)
    add zero nsmul neg sub zsmul inferInstance (fun (f : D ⟶ E) ↦ Hom.hom f) (homAddCommGroup_laws D E).2.2.2.2.2.2 rfl
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Addition of face-descent morphisms is addition of the underlying `O_0`-module maps. -/
theorem homAddCommGroup_add_hom {D E : FaceDescent C J O} (f g : D ⟶ E) :
    Hom.hom ((homAddCommGroup D E).add f g) = (Hom.hom f) + (Hom.hom g) :=
  rfl

/-- Composition distributes over the specified addition on face-descent morphisms. -/
private theorem preadditive_laws :
    (∀ (D E F : FaceDescent C J O) (f f' : D ⟶ E) (g : E ⟶ F),
      (homAddCommGroup D E).add f f' ≫ g =
        (homAddCommGroup D F).add (f ≫ g) (f' ≫ g)) ∧
    (∀ (D E F : FaceDescent C J O) (f : D ⟶ E) (g g' : E ⟶ F),
      f ≫ (homAddCommGroup E F).add g g' =
        (homAddCommGroup D F).add (f ≫ g) (f ≫ g')) :=
  sorry

end FaceDescent

/-- Face-descent pairs form a preadditive category via their underlying `O_0`-module maps. -/
@[reducible]
def instPreadditiveFaceDescent : Preadditive (FaceDescent C J O) where
  homGroup D E := FaceDescent.homAddCommGroup D E
  add_comp := (FaceDescent.preadditive_laws (C := C) (J := J) (O := O)).1
  comp_add := (FaceDescent.preadditive_laws (C := C) (J := J) (O := O)).2

variable [instFlatCoface0 : ToposHom.IsFlat
    (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2)))]
variable [instFlatCoface1 : ToposHom.IsFlat
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2)))]
variable [instSheafifyAddCommGrp : HasSheafify ((J ⦋0⦌).toGrothendieck) AddCommGrpCat.{w}]
variable [instLocallyBijectiveAddCommGrp :
    ((J ⦋0⦌).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Pullback along `f_{δ 0}` preserves finite limits. -/
@[implicit_reducible]
def preservesFiniteLimits_cofacePullback0 :
    PreservesFiniteLimits (cofacePullback C J O (0 : Fin 2)) :=
  (ToposHom.IsFlat.exactPullback
    (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2)))).property.1

/-- Pullback along `f_{δ 1}` preserves finite limits. -/
@[implicit_reducible]
def preservesFiniteLimits_cofacePullback1 :
    PreservesFiniteLimits (cofacePullback C J O (1 : Fin 2)) :=
  (ToposHom.IsFlat.exactPullback
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2)))).property.1

/-- Pullback along `f_{δ 0}` preserves finite colimits. -/
@[implicit_reducible]
def preservesFiniteColimits_cofacePullback0 :
    PreservesFiniteColimits (cofacePullback C J O (0 : Fin 2)) :=
  (ToposHom.IsFlat.exactPullback
    (ringedToposMap C J O (SimplexCategory.δ (0 : Fin 2)))).property.2

/-- Pullback along `f_{δ 1}` preserves finite colimits. -/
@[implicit_reducible]
def preservesFiniteColimits_cofacePullback1 :
    PreservesFiniteColimits (cofacePullback C J O (1 : Fin 2)) :=
  (ToposHom.IsFlat.exactPullback
    (ringedToposMap C J O (SimplexCategory.δ (1 : Fin 2)))).property.2

namespace FaceDescent

variable {C J O}

/-- The coface isomorphism on the kernel of an `O_0`-module map, via kernel comparison of the
two exact 1-coface pullbacks. -/
def kernelIso {D E : FaceDescent C J O} (f : D ⟶ E) :
    (cofacePullback C J O (1 : Fin 2)).obj (Limits.kernel (Hom.hom f)) ≅
      (cofacePullback C J O (0 : Fin 2)).obj (Limits.kernel (Hom.hom f)) :=
  let limits0 := (preservesFiniteLimits_cofacePullback0 C J O).preservesFiniteLimits
  let zero0 := @Functor.preservesZeroMorphisms_of_preserves_terminal_object
    _ _ _ _ inferInstance inferInstance inferInstance inferInstance
    (cofacePullback C J O (0 : Fin 2))
    (PreservesLimitsOfShape.preservesLimit (self := limits0 _))
  let limits1 := (preservesFiniteLimits_cofacePullback1 C J O).preservesFiniteLimits
  let zero1 := @Functor.preservesZeroMorphisms_of_preserves_terminal_object
    _ _ _ _ inferInstance inferInstance inferInstance inferInstance
    (cofacePullback C J O (1 : Fin 2))
    (PreservesLimitsOfShape.preservesLimit (self := limits1 _))
  @PreservesKernel.iso _ _ inferInstance _ _ inferInstance
    (cofacePullback C J O (1 : Fin 2)) zero1 _ _ (Hom.hom f) inferInstance inferInstance
    (PreservesLimitsOfShape.preservesLimit (self := limits1 _)) ≪≫
    kernel.mapIso ((cofacePullback C J O (1 : Fin 2)).map (Hom.hom f))
      ((cofacePullback C J O (0 : Fin 2)).map (Hom.hom f)) D.iso E.iso (Hom.comm f) ≪≫
    (@PreservesKernel.iso _ _ inferInstance _ _ inferInstance
      (cofacePullback C J O (0 : Fin 2)) zero0 _ _ (Hom.hom f) inferInstance inferInstance
      (PreservesLimitsOfShape.preservesLimit (self := limits0 _))).symm

/-- The coface comparison on the kernel satisfies the degree-two cocycle. -/
private theorem kernel_cocycle {D E : FaceDescent C J O} (f : D ⟶ E) :
    cocycleLeft C J O (kernelIso f) = cocycleRight C J O (kernelIso f) :=
  sorry

/-- The kernel of a morphism of face-descent pairs, with underlying module `kernel (Hom.hom f)`. -/
def kernel {D E : FaceDescent C J O} (f : D ⟶ E) : FaceDescent C J O :=
  ofIso (Limits.kernel (Hom.hom f)) (kernelIso f) (kernel_cocycle f)

/-- The underlying `O_0`-module of `kernel f` is `kernel (Hom.hom f)`. -/
theorem kernel_module {D E : FaceDescent C J O} (f : D ⟶ E) :
    (kernel f).module = Limits.kernel (Hom.hom f) :=
  rfl

/-- The underlying kernel inclusion commutes with the coface isomorphisms. -/
private theorem kernelι_comm {D E : FaceDescent C J O} (f : D ⟶ E) :
    (cofacePullback C J O (1 : Fin 2)).map (Limits.kernel.ι (Hom.hom f)) ≫ D.iso.hom =
      (kernel f).iso.hom ≫ (cofacePullback C J O (0 : Fin 2)).map (Limits.kernel.ι (Hom.hom f)) :=
  sorry

/-- The kernel inclusion of a morphism of face-descent pairs. -/
def kernelι {D E : FaceDescent C J O} (f : D ⟶ E) : kernel f ⟶ D :=
  homMk (Limits.kernel.ι (Hom.hom f)) (kernelι_comm f)

/-- The underlying map of `kernelι f` is `kernel.ι (Hom.hom f)`. -/
theorem kernelι_hom {D E : FaceDescent C J O} (f : D ⟶ E) :
    Hom.hom (kernelι f) = Limits.kernel.ι (Hom.hom f) :=
  rfl

/-- The kernel inclusion composes to zero with the original morphism. -/
theorem kernelι_comp {D E : FaceDescent C J O} (f : D ⟶ E) : kernelι f ≫ f = (homAddCommGroup (kernel f) E).zero :=
  sorry

/-- An underlying composite that is zero remains zero on `O_0`-modules. -/
private theorem hom_comp_eq_zero {W D E : FaceDescent C J O} {f : D ⟶ E} {k : W ⟶ D}
    (h : k ≫ f = (homAddCommGroup W E).zero) : (Hom.hom k) ≫ (Hom.hom f) = 0 :=
  sorry

/-- The universal underlying-module map for the kernel commutes with the coface isomorphisms. -/
private theorem kernelLift_comm {W D E : FaceDescent C J O} (f : D ⟶ E) (k : W ⟶ D) (h : k ≫ f = (homAddCommGroup W E).zero) :
    (cofacePullback C J O (1 : Fin 2)).map (Limits.kernel.lift (Hom.hom f) (Hom.hom k) (hom_comp_eq_zero h)) ≫ (kernel f).iso.hom =
      W.iso.hom ≫ (cofacePullback C J O (0 : Fin 2)).map (Limits.kernel.lift (Hom.hom f) (Hom.hom k) (hom_comp_eq_zero h)) :=
  sorry

/-- The universal map into the kernel of a morphism of face-descent pairs. -/
def kernelLift {W D E : FaceDescent C J O} (f : D ⟶ E) (k : W ⟶ D) (h : k ≫ f = (homAddCommGroup W E).zero) :
    W ⟶ kernel f :=
  homMk (Limits.kernel.lift (Hom.hom f) (Hom.hom k) (hom_comp_eq_zero h)) (kernelLift_comm f k h)

/-- The underlying map of `kernelLift` is `kernel.lift` of the underlying maps. -/
theorem kernelLift_hom {W D E : FaceDescent C J O} (f : D ⟶ E) (k : W ⟶ D)
    (h : k ≫ f = (homAddCommGroup W E).zero) :
    Hom.hom (kernelLift f k h) = Limits.kernel.lift (Hom.hom f) (Hom.hom k) (hom_comp_eq_zero h) :=
  rfl

/-- The kernel fork of a morphism of face-descent pairs. -/
def kerFork {D E : FaceDescent C J O} (f : D ⟶ E) : @KernelFork _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f :=
  @KernelFork.ofι _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f _ (kernelι f) (kernelι_comp f)

/-- The explicit kernel lift satisfies factorization and uniqueness for the kernel fork. -/
private theorem kerFork_laws {D E : FaceDescent C J O} (f : D ⟶ E) :
    (∀ (s : @KernelFork _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f) j,
      kernelLift f (Fork.ι s) (@KernelFork.condition _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f s) ≫ (kerFork f).π.app j = s.π.app j) ∧
    (∀ (s : @KernelFork _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f) (m : s.pt ⟶ (kerFork f).pt),
      (∀ j, m ≫ (kerFork f).π.app j = s.π.app j) →
        m = kernelLift f (Fork.ι s) (@KernelFork.condition _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f s)) :=
  sorry

/-- The named kernel fork is a limit cone. -/
def isLimit_kerFork {D E : FaceDescent C J O} (f : D ⟶ E) : IsLimit (kerFork f) where
  lift s := kernelLift f (Fork.ι s) (@KernelFork.condition _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f s)
  fac := (kerFork_laws f).1
  uniq := (kerFork_laws f).2

/-- The coface isomorphism on the cokernel of an `O_0`-module map, via cokernel comparison of
the two exact 1-coface pullbacks. -/
def cokernelIso {D E : FaceDescent C J O} (f : D ⟶ E) :
    (cofacePullback C J O (1 : Fin 2)).obj (Limits.cokernel (Hom.hom f)) ≅
      (cofacePullback C J O (0 : Fin 2)).obj (Limits.cokernel (Hom.hom f)) :=
  let limits0 := (preservesFiniteLimits_cofacePullback0 C J O).preservesFiniteLimits
  let zero0 := @Functor.preservesZeroMorphisms_of_preserves_terminal_object
    _ _ _ _ inferInstance inferInstance inferInstance inferInstance
    (cofacePullback C J O (0 : Fin 2))
    (PreservesLimitsOfShape.preservesLimit (self := limits0 _))
  let colimits0 := (preservesFiniteColimits_cofacePullback0 C J O).preservesFiniteColimits
  let limits1 := (preservesFiniteLimits_cofacePullback1 C J O).preservesFiniteLimits
  let zero1 := @Functor.preservesZeroMorphisms_of_preserves_terminal_object
    _ _ _ _ inferInstance inferInstance inferInstance inferInstance
    (cofacePullback C J O (1 : Fin 2))
    (PreservesLimitsOfShape.preservesLimit (self := limits1 _))
  let colimits1 := (preservesFiniteColimits_cofacePullback1 C J O).preservesFiniteColimits
  @PreservesCokernel.iso _ _ inferInstance _ _ inferInstance
    (cofacePullback C J O (1 : Fin 2)) zero1 _ _ (Hom.hom f) inferInstance inferInstance
    (PreservesColimitsOfShape.preservesColimit (self := colimits1 _)) ≪≫
    cokernel.mapIso ((cofacePullback C J O (1 : Fin 2)).map (Hom.hom f))
      ((cofacePullback C J O (0 : Fin 2)).map (Hom.hom f)) D.iso E.iso (Hom.comm f) ≪≫
    (@PreservesCokernel.iso _ _ inferInstance _ _ inferInstance
      (cofacePullback C J O (0 : Fin 2)) zero0 _ _ (Hom.hom f) inferInstance inferInstance
      (PreservesColimitsOfShape.preservesColimit (self := colimits0 _))).symm

/-- The coface comparison on the cokernel satisfies the degree-two cocycle. -/
private theorem cokernel_cocycle {D E : FaceDescent C J O} (f : D ⟶ E) :
    cocycleLeft C J O (cokernelIso f) = cocycleRight C J O (cokernelIso f) :=
  sorry

/-- The cokernel of a morphism of face-descent pairs, with underlying module `cokernel (Hom.hom f)`. -/
def cokernel {D E : FaceDescent C J O} (f : D ⟶ E) : FaceDescent C J O :=
  ofIso (Limits.cokernel (Hom.hom f)) (cokernelIso f) (cokernel_cocycle f)

/-- The underlying `O_0`-module of `cokernel f` is `cokernel (Hom.hom f)`. -/
theorem cokernel_module {D E : FaceDescent C J O} (f : D ⟶ E) :
    (cokernel f).module = Limits.cokernel (Hom.hom f) :=
  rfl

/-- The underlying cokernel projection commutes with the coface isomorphisms. -/
private theorem cokernelπ_comm {D E : FaceDescent C J O} (f : D ⟶ E) :
    (cofacePullback C J O (1 : Fin 2)).map (Limits.cokernel.π (Hom.hom f)) ≫ (cokernel f).iso.hom =
      E.iso.hom ≫ (cofacePullback C J O (0 : Fin 2)).map (Limits.cokernel.π (Hom.hom f)) :=
  sorry

/-- The cokernel projection of a morphism of face-descent pairs. -/
def cokernelπ {D E : FaceDescent C J O} (f : D ⟶ E) : E ⟶ cokernel f :=
  homMk (Limits.cokernel.π (Hom.hom f)) (cokernelπ_comm f)

/-- The underlying map of `cokernelπ f` is `cokernel.π (Hom.hom f)`. -/
theorem cokernelπ_hom {D E : FaceDescent C J O} (f : D ⟶ E) :
    Hom.hom (cokernelπ f) = Limits.cokernel.π (Hom.hom f) :=
  rfl

/-- The original morphism composes to zero with the cokernel projection. -/
theorem cokernelπ_comp {D E : FaceDescent C J O} (f : D ⟶ E) : f ≫ cokernelπ f = (homAddCommGroup D (cokernel f)).zero :=
  sorry

/-- An underlying composite that is zero remains zero on `O_0`-modules, dual form. -/
private theorem hom_comp_eq_zero' {D E T : FaceDescent C J O} {f : D ⟶ E} {g : E ⟶ T}
    (h : f ≫ g = (homAddCommGroup D T).zero) : (Hom.hom f) ≫ (Hom.hom g) = 0 :=
  sorry

/-- The universal underlying-module map for the cokernel commutes with the coface isomorphisms. -/
private theorem cokernelDesc_comm {D E T : FaceDescent C J O} (f : D ⟶ E) (g : E ⟶ T) (h : f ≫ g = (homAddCommGroup D T).zero) :
    (cofacePullback C J O (1 : Fin 2)).map (Limits.cokernel.desc (Hom.hom f) (Hom.hom g) (hom_comp_eq_zero' h)) ≫ T.iso.hom =
      (cokernel f).iso.hom ≫ (cofacePullback C J O (0 : Fin 2)).map (Limits.cokernel.desc (Hom.hom f) (Hom.hom g) (hom_comp_eq_zero' h)) :=
  sorry

/-- The universal map out of the cokernel of a morphism of face-descent pairs. -/
def cokernelDesc {D E T : FaceDescent C J O} (f : D ⟶ E) (g : E ⟶ T) (h : f ≫ g = (homAddCommGroup D T).zero) :
    cokernel f ⟶ T :=
  homMk (Limits.cokernel.desc (Hom.hom f) (Hom.hom g) (hom_comp_eq_zero' h)) (cokernelDesc_comm f g h)

/-- The underlying map of `cokernelDesc` is `cokernel.desc` of the underlying maps. -/
theorem cokernelDesc_hom {D E T : FaceDescent C J O} (f : D ⟶ E) (g : E ⟶ T)
    (h : f ≫ g = (homAddCommGroup D T).zero) :
    Hom.hom (cokernelDesc f g h) = Limits.cokernel.desc (Hom.hom f) (Hom.hom g) (hom_comp_eq_zero' h) :=
  rfl

/-- The cokernel cofork of a morphism of face-descent pairs. -/
def cokerCofork {D E : FaceDescent C J O} (f : D ⟶ E) : @CokernelCofork _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f :=
  @CokernelCofork.ofπ _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f _ (cokernelπ f) (cokernelπ_comp f)

/-- The explicit cokernel descent satisfies factorization and uniqueness for the cokernel cofork. -/
private theorem cokerCofork_laws {D E : FaceDescent C J O} (f : D ⟶ E) :
    (∀ (s : @CokernelCofork _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f) j,
      (cokerCofork f).ι.app j ≫ cokernelDesc f (Cofork.π s) (@CokernelCofork.condition _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f s) =
        s.ι.app j) ∧
    (∀ (s : @CokernelCofork _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f) (m : (cokerCofork f).pt ⟶ s.pt),
      (∀ j, (cokerCofork f).ι.app j ≫ m = s.ι.app j) →
        m = cokernelDesc f (Cofork.π s) (@CokernelCofork.condition _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f s)) :=
  sorry

/-- The named cokernel cofork is a colimit cocone. -/
def isColimit_cokerCofork {D E : FaceDescent C J O} (f : D ⟶ E) :
    IsColimit (cokerCofork f) where
  desc s := cokernelDesc f (Cofork.π s) (@CokernelCofork.condition _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) _ _ f s)
  fac := (cokerCofork_laws f).1
  uniq := (cokerCofork_laws f).2

end FaceDescent

/-- Face-descent pairs have kernels, computed in `Mod(O_0)` and reassembled by `kernelIso`. -/
@[implicit_reducible]
def instHasKernelsFaceDescent_of_isFlat_delta01 : @HasKernels (FaceDescent C J O) _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) :=
  @HasKernels.mk _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O))
    (fun f ↦ HasLimit.mk { cone := FaceDescent.kerFork f, isLimit := FaceDescent.isLimit_kerFork f })

/-- Face-descent pairs have cokernels, computed in `Mod(O_0)` and reassembled by `cokernelIso`. -/
@[implicit_reducible]
def instHasCokernelsFaceDescent_of_isFlat_delta01 : @HasCokernels (FaceDescent C J O) _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) :=
  @HasCokernels.mk _ _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O))
    (fun f ↦ HasColimit.mk
      { cocone := FaceDescent.cokerCofork f, isColimit := FaceDescent.isColimit_cokerCofork f })

include instFlatCoface0 instFlatCoface1 instSheafifyAddCommGrp instLocallyBijectiveAddCommGrp in
/-- With exact degree-one coface pullbacks, all monomorphisms and epimorphisms of
face-descent data are normal and finite products exist. -/
private theorem FaceDescent.abelian_laws :
    @IsNormalMonoCategory (FaceDescent C J O) _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) ∧
      @IsNormalEpiCategory (FaceDescent C J O) _ (@Preadditive.preadditiveHasZeroMorphisms _ _ (instPreadditiveFaceDescent C J O)) ∧ HasFiniteProducts (FaceDescent C J O) :=
  sorry

/-- If `f_{δ 0}` and `f_{δ 1}` are flat, the category of face-descent pairs is abelian. -/
@[implicit_reducible]
def instAbelianFaceDescent_of_isFlat_delta01 : Abelian (FaceDescent C J O) where
  toPreadditive := instPreadditiveFaceDescent C J O
  has_kernels := instHasKernelsFaceDescent_of_isFlat_delta01 C J O
  has_cokernels := instHasCokernelsFaceDescent_of_isFlat_delta01 C J O
  toIsNormalMonoCategory := (FaceDescent.abelian_laws C J O).1
  toIsNormalEpiCategory := (FaceDescent.abelian_laws C J O).2.1
  has_finite_products := (FaceDescent.abelian_laws C J O).2.2

end CategoryTheory.SimplicialSites.Module


