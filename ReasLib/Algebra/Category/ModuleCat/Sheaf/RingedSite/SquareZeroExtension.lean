/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Derivation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Tactic.Ring

/-!
# Square-zero lifting on a ringed site

The core API treats an arbitrary lifting problem of commutative ring sheaves.  Compatible
sections are recovered by specializing the morphism being lifted to an identity. Relative to a
chosen lift, perturbation and the canonical difference derivation give an explicit equivalence
between relative derivations and all compatible lifts; no group-action instance is asserted until
the derivation layer itself carries the needed additive structure.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped RelativeDerivation

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R B A Q : Sheaf J CommRingCat.{w}}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

namespace KernelIdeal

/-- The kernel ideal of `π` is square zero sectionwise, in the standard mathlib form
`I ^ 2 = ⊥`. -/
@[stacks 04BP "square-zero kernel ideal", stacks 01UP "square-zero kernel ideal"]
abbrev IsSquareZero (π : A ⟶ Q) : Prop :=
  ∀ U : Cᵒᵖ, sectionIdeal π U ^ 2 = ⊥

/-- Products of sections of the categorical kernel vanish when its section ideals are square
zero. -/
theorem ιApp_mul_ιApp_eq_zero (π : A ⟶ Q) (hzero : IsSquareZero π)
    (U : Cᵒᵖ) (x y : (sheaf π).val.obj U) :
    ιApp π U x * ιApp π U y = 0 := by
  have hmem := Ideal.mul_mem_mul (ιApp_mem_sectionIdeal π U x)
    (ιApp_mem_sectionIdeal π U y)
  rw [← pow_two, hzero U] at hmem
  exact hmem

/-- The sectionwise kernel ideals are square zero exactly when every pair of sections of the
categorical kernel has zero product after inclusion. -/
@[stacks 04BP "categorical square-zero criterion", stacks 01UP "categorical square-zero criterion"]
theorem isSquareZero_iff (π : A ⟶ Q) :
    IsSquareZero π ↔
      ∀ U : Cᵒᵖ, ∀ x y : (sheaf π).val.obj U,
        ιApp π U x * ιApp π U y = 0 := by
  constructor
  · exact ιApp_mul_ιApp_eq_zero π
  · intro h U
    rw [pow_two]
    refine le_antisymm ?_ bot_le
    refine Ideal.mul_le.mpr ?_
    intro x hx y hy
    obtain ⟨x', rfl⟩ := (mem_sectionIdeal_iff π U x).mp hx
    obtain ⟨y', rfl⟩ := (mem_sectionIdeal_iff π U y).mp hy
    exact h U x' y'

/-- Restriction of the kernel ideal along a lift `l : B ⟶ A`, regarded as a `B`-module sheaf. -/
abbrev restrict (π : A ⟶ Q) (l : B ⟶ A) : SheafOfModules (ringSheaf J B) :=
  (restrictionAlong l).obj (sheaf π)

/-- The kernel-ideal inclusion after restriction of scalars along `l`. -/
abbrev restrictedι (π : A ⟶ Q) (l : B ⟶ A) :
    restrict π l ⟶ (restrictionAlong l).obj (unitModule J A) :=
  (restrictionAlong l).map (ι π)

/-- The value of the restricted kernel-ideal inclusion on a section over `U`. -/
abbrev restrictedιApp (π : A ⟶ Q) (l : B ⟶ A)
    (U : Cᵒᵖ) (x : (restrict π l).val.obj U) : A.obj.obj U :=
  (restrictedι π l).val.app U x

end KernelIdeal

variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

namespace SquareZeroExtension

/-- A morphism `l : B ⟶ A` is a compatible `R`-algebra lift of `f : B ⟶ Q` through
`π : A ⟶ Q`. -/
abbrev IsLift (α : R ⟶ B) (β : R ⟶ A) (π : A ⟶ Q) (f : B ⟶ Q)
    (l : B ⟶ A) : Prop :=
  l ≫ π = f ∧ α ≫ l = β

/-- The bundled type of compatible `R`-algebra lifts of `f` through `π`. -/
@[stacks 04BP "compatible algebra lifts", stacks 01UP "compatible algebra lifts"]
abbrev Lift (α : R ⟶ B) (β : R ⟶ A) (π : A ⟶ Q) (f : B ⟶ Q) :=
  { l : B ⟶ A // IsLift α β π f l }

namespace Lift

/-- The underlying morphism of a bundled compatible lift. -/
abbrev hom {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l : Lift α β π f) : B ⟶ A :=
  l.1

/-- Bundled compatible lifts are equal when their underlying morphisms are equal. -/
@[ext]
theorem ext {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    {l l' : Lift α β π f} (h : l.hom = l'.hom) : l = l' := by
  exact Subtype.ext h

end Lift

/-- A relative derivation `D` is the difference from `l` to `l'` when the expected formula holds
on every object of the site. -/
abbrev IsDifference (α : R ⟶ B) (π : A ⟶ Q) (l l' : B ⟶ A)
    (D : Der[α ; KernelIdeal.restrict π l]) : Prop :=
  ∀ U : Cᵒᵖ, ∀ x : B.obj.obj U,
    l'.hom.app U x = l.hom.app U x + KernelIdeal.restrictedιApp π l U (D.d x)

/-- The difference of two ring-sheaf morphisms as a morphism of their underlying additive
unit-module sheaves. -/
@[stacks 01UP "underlying additive difference",
  stacks 04BP "underlying additive difference"]
noncomputable def additiveDifference (l l' : B ⟶ A) :
    (SheafOfModules.toSheaf (ringSheaf J B)).obj (unitModule J B) ⟶
      (SheafOfModules.toSheaf (ringSheaf J A)).obj (unitModule J A) :=
  SheafOfModules.unitUnderlyingMap (ringSheafMap l') -
    SheafOfModules.unitUnderlyingMap (ringSheafMap l)

/-- The underlying additive difference acts sectionwise by subtraction in the target ring. -/
@[simp, stacks 01UP "underlying additive difference on sections",
  stacks 04BP "underlying additive difference on sections"]
theorem additiveDifference_app_apply (l l' : B ⟶ A)
    (U : Cᵒᵖ) (x : B.obj.obj U) :
    (additiveDifference l l').hom.app U x =
      l'.hom.app U x - l.hom.app U x := by
  rfl

/-- If two ring-sheaf morphisms agree after composition, their underlying additive difference
factors through the kernel ideal. -/
@[stacks 01UP "additive difference vanishes after the quotient map",
  stacks 04BP "additive difference vanishes after the quotient map"]
theorem additiveDifference_comp_kernelMap (l l' : B ⟶ A) (π : A ⟶ Q)
    (h : l ≫ π = l' ≫ π) :
    additiveDifference l l' ≫
        (SheafOfModules.toSheaf (ringSheaf J A)).map (KernelIdeal.map π) = 0 := by
  ext U x
  change π.hom.app U ((additiveDifference l l').hom.app U x) = 0
  rw [additiveDifference_app_apply, map_sub]
  have hx := congrArg (fun g : B ⟶ Q ↦ g.hom.app U x) h
  change π.hom.app U (l.hom.app U x) = π.hom.app U (l'.hom.app U x) at hx
  rw [hx, sub_self]

/-- The local function `x ↦ l(x) + ι(Dx)` underlying perturbation of a lift. -/
abbrev perturbApply (α : R ⟶ B) (π : A ⟶ Q) (l : B ⟶ A)
    (D : Der[α ; KernelIdeal.restrict π l]) (U : Cᵒᵖ) (x : B.obj.obj U) :
    A.obj.obj U :=
  l.hom.app U x + KernelIdeal.restrictedιApp π l U (D.d x)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The local perturbation function preserves zero. -/
theorem perturbApply_zero (α : R ⟶ B) (π : A ⟶ Q) (l : B ⟶ A)
    (D : Der[α ; KernelIdeal.restrict π l]) (U : Cᵒᵖ) :
    perturbApply α π l D U 0 = 0 := by
  have hι : KernelIdeal.restrictedιApp π l U 0 = 0 :=
    ((KernelIdeal.restrictedι π l).val.app U).hom.map_zero
  dsimp only [perturbApply]
  rw [(l.hom.app U).hom.map_zero, D.d.map_zero, hι, add_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The local perturbation function preserves one. -/
theorem perturbApply_one (α : R ⟶ B) (π : A ⟶ Q) (l : B ⟶ A)
    (D : Der[α ; KernelIdeal.restrict π l]) (U : Cᵒᵖ) :
    perturbApply α π l D U 1 = 1 := by
  have hι : KernelIdeal.restrictedιApp π l U 0 = 0 :=
    ((KernelIdeal.restrictedι π l).val.app U).hom.map_zero
  dsimp only [perturbApply]
  rw [(l.hom.app U).hom.map_one, D.d_one U, hι, add_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The local perturbation function preserves addition. -/
theorem perturbApply_add (α : R ⟶ B) (π : A ⟶ Q) (l : B ⟶ A)
    (D : Der[α ; KernelIdeal.restrict π l]) (U : Cᵒᵖ) (x y : B.obj.obj U) :
    perturbApply α π l D U (x + y) =
      perturbApply α π l D U x + perturbApply α π l D U y := by
  dsimp only [perturbApply, KernelIdeal.restrictedιApp]
  rw [(l.hom.app U).hom.map_add, D.d.map_add,
    ((KernelIdeal.restrictedι π l).val.app U).hom.map_add]
  abel

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The local perturbation function preserves multiplication when the kernel ideal is square
zero. -/
theorem perturbApply_mul (α : R ⟶ B) (π : A ⟶ Q) (l : B ⟶ A)
    (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l]) (U : Cᵒᵖ) (x y : B.obj.obj U) :
    perturbApply α π l D U (x * y) =
      perturbApply α π l D U x * perturbApply α π l D U y := by
  have hmul := KernelIdeal.ιApp_mul_ιApp_eq_zero π hzero U (D.d x) (D.d y)
  change KernelIdeal.restrictedιApp π l U (D.d x) *
    KernelIdeal.restrictedιApp π l U (D.d y) = 0 at hmul
  dsimp only [perturbApply, KernelIdeal.restrictedιApp]
  rw [(l.hom.app U).hom.map_mul, D.d_mul x y,
    ((KernelIdeal.restrictedι π l).val.app U).hom.map_add,
    ((KernelIdeal.restrictedι π l).val.app U).hom.map_smul x,
    ((KernelIdeal.restrictedι π l).val.app U).hom.map_smul y]
  change l.hom.app U x * l.hom.app U y +
      (l.hom.app U x * KernelIdeal.restrictedιApp π l U (D.d y) +
        l.hom.app U y * KernelIdeal.restrictedιApp π l U (D.d x)) = _
  rw [add_mul, mul_add, mul_add, hmul]
  ring

/-- The ring homomorphism on one object of the site obtained by perturbing a lift. -/
def perturbRingHom (α : R ⟶ B) (π : A ⟶ Q) (l : B ⟶ A)
    (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l]) (U : Cᵒᵖ) :
    B.obj.obj U →+* A.obj.obj U where
  toFun := perturbApply α π l D U
  map_zero' := perturbApply_zero α π l D U
  map_one' := perturbApply_one α π l D U
  map_add' := perturbApply_add α π l D U
  map_mul' := perturbApply_mul α π l hzero D U

/-- The component over one object of the morphism obtained by perturbing a lift. -/
abbrev perturbApp (α : R ⟶ B) (π : A ⟶ Q) (l : B ⟶ A)
    (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l]) (U : Cᵒᵖ) :
    B.obj.obj U ⟶ A.obj.obj U :=
  CommRingCat.ofHom (perturbRingHom α π l hzero D U)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The components of a perturbed lift commute with restriction maps. -/
theorem perturbApp_naturality (α : R ⟶ B) (π : A ⟶ Q) (l : B ⟶ A)
    (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l]) {U V : Cᵒᵖ} (i : U ⟶ V) :
    B.obj.map i ≫ perturbApp α π l hzero D V =
      perturbApp α π l hzero D U ≫ A.obj.map i := by
  ext x
  change perturbApply α π l D V (B.obj.map i x) =
    A.obj.map i (perturbApply α π l D U x)
  simp only [perturbApply, map_add]
  have hd : D.d (B.obj.map i x) =
      (KernelIdeal.restrict π l).val.map i (D.d x) := D.d_map i x
  rw [hd]
  congr 1
  · exact ConcreteCategory.congr_hom (l.hom.naturality i) x
  · exact PresheafOfModules.naturality_apply (KernelIdeal.restrictedι π l).val i (D.d x)

/-- The explicit morphism obtained by perturbing `l` by the relative derivation `D`. -/
@[stacks 04BP "perturbation of a lift", stacks 01UP "perturbation of a lift"]
noncomputable def perturb (α : R ⟶ B) (π : A ⟶ Q) (l : B ⟶ A)
    (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l]) : B ⟶ A :=
  ObjectProperty.homMk
    { app U := perturbApp α π l hzero D U
      naturality {U V} i := perturbApp_naturality α π l hzero D (U := U) (V := V) i }

/-- The perturbed morphism has the expected value on every local section. -/
@[simp]
theorem perturb_apply (α : R ⟶ B) (π : A ⟶ Q) (l : B ⟶ A)
    (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l]) (U : Cᵒᵖ) (x : B.obj.obj U) :
    (perturb α π l hzero D).hom.app U x = perturbApply α π l D U x := by
  rfl

/-- Perturbation realizes the specified derivation as its difference from the original lift. -/
theorem perturb_isDifference (α : R ⟶ B) (π : A ⟶ Q) (l : B ⟶ A)
    (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l]) :
    IsDifference α π l (perturb α π l hzero D) D := by
  intro U x
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Perturbing a compatible lift by a relative derivation gives another compatible lift. -/
theorem perturb_isLift (α : R ⟶ B) (β : R ⟶ A) (π : A ⟶ Q) (f : B ⟶ Q)
    (l : B ⟶ A) (hl : IsLift α β π f l) (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l]) :
    IsLift α β π f (perturb α π l hzero D) := by
  constructor
  · show perturb α π l hzero D ≫ π = f
    rw [← hl.1]
    ext U x
    change π.hom.app U ((perturb α π l hzero D).hom.app U x) =
      π.hom.app U (l.hom.app U x)
    rw [perturb_apply]
    change π.hom.app U (l.hom.app U x + KernelIdeal.ιApp π U (D.d x)) = _
    rw [map_add]
    have hz := KernelIdeal.ιApp_mem_sectionIdeal π U (D.d x)
    change π.hom.app U (KernelIdeal.ιApp π U (D.d x)) = 0 at hz
    rw [hz, add_zero]
  · show α ≫ perturb α π l hzero D = β
    rw [← hl.2]
    ext U x
    change (perturb α π l hzero D).hom.app U (α.hom.app U x) =
      l.hom.app U (α.hom.app U x)
    rw [perturb_apply]
    have hι : KernelIdeal.restrictedιApp π l U 0 = 0 :=
      ((KernelIdeal.restrictedι π l).val.app U).hom.map_zero
    have hd : D.d (α.hom.app U x) = 0 := PresheafOfModules.Derivation'.d_app D x
    dsimp only [perturbApply]
    rw [hd, hι, add_zero]

/-- A morphism with the perturbation formula is equal to the explicit perturbation. -/
theorem eq_perturb (α : R ⟶ B) (π : A ⟶ Q) (l l' : B ⟶ A)
    (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l]) (hD : IsDifference α π l l' D) :
    l' = perturb α π l hzero D := by
  ext U x
  exact hD U x

namespace Lift

/-- Perturbation as a map between bundled compatible lifts. -/
noncomputable def perturb {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l.hom]) : Lift α β π f :=
  ⟨SquareZeroExtension.perturb α π l.hom hzero D,
    perturb_isLift α β π f l.hom l.2 hzero D⟩

/-- The underlying morphism of a bundled perturbation is the explicit perturbed morphism. -/
@[simp]
theorem perturb_hom {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l.hom]) :
    (l.perturb hzero D).hom = SquareZeroExtension.perturb α π l.hom hzero D := by
  rfl

/-- The pointed perturbation map from derivations at `l` to all compatible lifts. -/
noncomputable def perturbMap {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π) :
    Der[α ; KernelIdeal.restrict π l.hom] → Lift α β π f :=
  fun D ↦ l.perturb hzero D

/-- The pointed perturbation map is injective. -/
theorem perturbMap_injective {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π) :
    Function.Injective (l.perturbMap hzero) := by
  intro D E h
  ext U x
  apply KernelIdeal.ιApp_injective π U
  have hx := congrArg (fun k : Lift α β π f ↦ k.hom.hom.app U x) h
  change l.hom.hom.app U x + KernelIdeal.ιApp π U (D.d x) =
    l.hom.hom.app U x + KernelIdeal.ιApp π U (E.d x) at hx
  exact add_left_cancel hx

/-- A relative derivation produces a unique compatible lift with that difference from `l`. -/
theorem existsUnique_perturb {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l.hom]) :
    ∃! l' : Lift α β π f, IsDifference α π l.hom l'.hom D := by
  refine ⟨l.perturb hzero D, perturb_isDifference α π l.hom hzero D, ?_⟩
  intro l' hD
  apply Lift.ext
  exact eq_perturb α π l.hom l'.hom hzero D hD

/-- The underlying additive difference between two compatible lifts, factored canonically
through the kernel ideal. -/
@[stacks 01UP "difference map to the kernel ideal",
  stacks 04BP "difference map to the kernel ideal"]
noncomputable def differenceToKernel
    {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) :
    (SheafOfModules.toSheaf (ringSheaf J B)).obj (unitModule J B) ⟶
      (SheafOfModules.toSheaf (ringSheaf J A)).obj (KernelIdeal.sheaf π) :=
  KernelIdeal.additiveLift π (additiveDifference l.hom l'.hom)
    (additiveDifference_comp_kernelMap l.hom l'.hom π
      (l.2.1.trans l'.2.1.symm))

/-- The additive difference map with target the kernel ideal restricted along the chosen base
lift. -/
@[stacks 01UP "restricted additive difference map",
  stacks 04BP "restricted additive difference map"]
noncomputable def differenceAdd
    {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) :
    (SheafOfModules.toSheaf (ringSheaf J B)).obj (unitModule J B) ⟶
      (SheafOfModules.toSheaf (ringSheaf J B)).obj
        (KernelIdeal.restrict π l.hom) :=
  l.differenceToKernel l' ≫
    ((SheafOfModules.restrictScalarsCompToSheaf.{w}
      (ringSheafMap l.hom)).app (KernelIdeal.sheaf π)).inv

/-- The value of the restricted additive difference on a local section, with its canonical
module-valued codomain exposed. -/
@[stacks 01UP "restricted additive difference on sections",
  stacks 04BP "restricted additive difference on sections"]
noncomputable abbrev differenceAddApply
    {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (U : Cᵒᵖ) (x : B.obj.obj U) :
    (KernelIdeal.restrict π l.hom).val.obj U :=
  (l.differenceAdd l').hom.app U x

/-- Including the restricted additive difference into `A` recovers sectionwise subtraction of
the two lifts. -/
@[simp, stacks 01UP "restricted additive difference specification",
  stacks 04BP "restricted additive difference specification"]
theorem differenceAdd_ιApp
    {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (U : Cᵒᵖ) (x : B.obj.obj U) :
    KernelIdeal.restrictedιApp π l.hom U
        (l.differenceAddApply l' U x) =
      (l'.hom).hom.app U x - (l.hom).hom.app U x := by
  change KernelIdeal.ιApp π U ((l.differenceToKernel l').hom.app U x) = _
  have h := congrArg (fun g ↦ g.hom.app U x)
    (KernelIdeal.additiveLift_comp_ι π (additiveDifference l.hom l'.hom)
      (additiveDifference_comp_kernelMap l.hom l'.hom π
        (l.2.1.trans l'.2.1.symm)))
  exact h.trans (additiveDifference_app_apply l.hom l'.hom U x)

/-- The restricted additive difference preserves addition on every object of the site. -/
@[stacks 01UP "additivity of the difference map",
  stacks 04BP "additivity of the difference map"]
theorem differenceAdd_add
    {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (U : Cᵒᵖ) (x y : B.obj.obj U) :
    l.differenceAddApply l' U (x + y) =
      l.differenceAddApply l' U x + l.differenceAddApply l' U y := by
  exact ((l.differenceAdd l').hom.app U).hom.map_add x y

/-- For a square-zero kernel, the restricted additive difference satisfies the Leibniz rule
relative to the chosen base lift. -/
@[stacks 01UP "Leibniz rule for the difference map",
  stacks 04BP "Leibniz rule for the difference map"]
theorem differenceAdd_mul
    {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π)
    (U : Cᵒᵖ) (x y : B.obj.obj U) :
    l.differenceAddApply l' U (x * y) =
      x • l.differenceAddApply l' U y +
        y • l.differenceAddApply l' U x := by
  apply KernelIdeal.ιApp_injective π U
  change KernelIdeal.restrictedιApp π l.hom U (l.differenceAddApply l' U (x * y)) =
    KernelIdeal.restrictedιApp π l.hom U
      (x • l.differenceAddApply l' U y + y • l.differenceAddApply l' U x)
  have hsmul (a : B.obj.obj U) (m : (KernelIdeal.restrict π l.hom).val.obj U) :
      KernelIdeal.restrictedιApp π l.hom U (a • m) =
        l.hom.hom.app U a * KernelIdeal.restrictedιApp π l.hom U m :=
    ((KernelIdeal.restrictedι π l.hom).val.app U).hom.map_smul a m
  have hadd (a b : (KernelIdeal.restrict π l.hom).val.obj U) :
      KernelIdeal.restrictedιApp π l.hom U (a + b) =
        KernelIdeal.restrictedιApp π l.hom U a + KernelIdeal.restrictedιApp π l.hom U b :=
    ((KernelIdeal.restrictedι π l.hom).val.app U).hom.map_add a b
  have hz := KernelIdeal.ιApp_mul_ιApp_eq_zero π hzero U
    (l.differenceAddApply l' U x) (l.differenceAddApply l' U y)
  change KernelIdeal.restrictedιApp π l.hom U (l.differenceAddApply l' U x) *
    KernelIdeal.restrictedιApp π l.hom U (l.differenceAddApply l' U y) = 0 at hz
  rw [differenceAdd_ιApp, differenceAdd_ιApp] at hz
  rw [hadd, hsmul, hsmul, differenceAdd_ιApp, differenceAdd_ιApp,
    differenceAdd_ιApp, map_mul, map_mul]
  calc
    _ = l.hom.hom.app U x * (l'.hom.hom.app U y - l.hom.hom.app U y) +
        l.hom.hom.app U y * (l'.hom.hom.app U x - l.hom.hom.app U x) +
        (l'.hom.hom.app U x - l.hom.hom.app U x) *
          (l'.hom.hom.app U y - l.hom.hom.app U y) := by ring
    _ = _ := by rw [hz, add_zero]

/-- The restricted additive difference vanishes on the common base ring. -/
@[stacks 01UP "relative law for the difference map",
  stacks 04BP "relative law for the difference map"]
theorem differenceAdd_base
    {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (U : Cᵒᵖ) (x : R.obj.obj U) :
    l.differenceAddApply l' U (α.hom.app U x) = 0 := by
  apply KernelIdeal.ιApp_injective π U
  change KernelIdeal.restrictedιApp π l.hom U
    (l.differenceAddApply l' U (α.hom.app U x)) = KernelIdeal.ιApp π U 0
  rw [differenceAdd_ιApp]
  have hl := congrArg (fun g : R ⟶ A ↦ g.hom.app U x) l.2.2
  have hl' := congrArg (fun g : R ⟶ A ↦ g.hom.app U x) l'.2.2
  change l.hom.hom.app U (α.hom.app U x) = β.hom.app U x at hl
  change l'.hom.hom.app U (α.hom.app U x) = β.hom.app U x at hl'
  rw [hl, hl']
  exact (sub_self _).trans (((KernelIdeal.ι π).val.app U).hom.map_zero).symm

/-- The objectwise relative derivation carried by the canonical restricted additive difference. -/
@[stacks 01UP "objectwise difference derivation",
  stacks 04BP "objectwise difference derivation"]
noncomputable def differenceApp
    {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π)
    (U : Cᵒᵖ) :
    ((KernelIdeal.restrict π l.hom).val.obj U).Derivation (α.hom.app U) :=
  ModuleCat.Derivation.mk
    (fun x ↦ l.differenceAddApply l' U x)
    (differenceAdd_add l l' U)
    (differenceAdd_mul l l' hzero U)
    (differenceAdd_base l l' U)

/-- The objectwise difference derivation has the restricted additive difference as its
underlying map. -/
@[simp, stacks 01UP "objectwise difference derivation formula",
  stacks 04BP "objectwise difference derivation formula"]
theorem differenceApp_apply
    {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π)
    (U : Cᵒᵖ) (x : B.obj.obj U) :
    (l.differenceApp l' hzero U).d x =
      l.differenceAddApply l' U x := by
  rfl

/-- The objectwise difference derivations commute with restriction maps. -/
@[stacks 01UP "naturality of the difference derivation",
  stacks 04BP "naturality of the difference derivation"]
theorem differenceApp_naturality
    {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π)
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : B.obj.obj U) :
    (l.differenceApp l' hzero V).d (B.obj.map i x) =
      (KernelIdeal.restrict π l.hom).val.map i
        ((l.differenceApp l' hzero U).d x) := by
  exact ConcreteCategory.congr_hom ((l.differenceAdd l').hom.naturality i) x

/-- The canonical relative derivation measuring the difference from `l` to `l'`. -/
@[stacks 01UP "difference derivation", stacks 04BP "difference derivation"]
noncomputable def difference {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π) :
    Der[α ; KernelIdeal.restrict π l.hom] :=
  PresheafOfModules.Derivation'.mk
    (fun U ↦ l.differenceApp l' hzero U)
    (fun _ _ i x ↦ differenceApp_naturality l l' hzero i x)

/-- The canonical difference derivation has the expected local difference formula. -/
@[stacks 01UP "difference specification", stacks 04BP "difference specification"]
theorem difference_spec {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π) :
    IsDifference α π l.hom l'.hom (l.difference l' hzero) := by
  intro U x
  change l'.hom.hom.app U x = l.hom.hom.app U x +
    KernelIdeal.restrictedιApp π l.hom U (l.differenceAddApply l' U x)
  rw [differenceAdd_ιApp]
  exact (add_sub_cancel _ _).symm

/-- A relative derivation is the canonical difference exactly when it has the local difference
formula. -/
@[stacks 01UP "difference uniqueness", stacks 04BP "difference uniqueness"]
theorem difference_eq_iff {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l.hom]) :
    l.difference l' hzero = D ↔ IsDifference α π l.hom l'.hom D := by
  constructor
  · intro h
    rw [← h]
    exact difference_spec l l' hzero
  · intro hD
    ext U x
    apply KernelIdeal.ιApp_injective π U
    exact add_left_cancel ((difference_spec l l' hzero U x).symm.trans (hD U x))

/-- Perturbing `l` by its canonical difference to `l'` recovers `l'`. -/
@[simp, stacks 01UP "perturb-difference law", stacks 04BP "perturb-difference law"]
theorem perturb_difference {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π) :
    l.perturb hzero (l.difference l' hzero) = l' := by
  apply Lift.ext
  exact (eq_perturb α π l.hom l'.hom hzero (l.difference l' hzero)
    (difference_spec l l' hzero)).symm

/-- The canonical difference from `l` to its perturbation by `D` is `D`. -/
@[simp, stacks 01UP "difference-perturb law", stacks 04BP "difference-perturb law"]
theorem difference_perturb {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π)
    (D : Der[α ; KernelIdeal.restrict π l.hom]) :
    l.difference (l.perturb hzero D) hzero = D := by
  exact (difference_eq_iff l (l.perturb hzero D) hzero D).mpr
    (perturb_isDifference α π l.hom hzero D)

/-- The pointed perturbation map is surjective. -/
theorem perturbMap_surjective {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π) :
    Function.Surjective (l.perturbMap hzero) := by
  intro l'
  exact ⟨l.difference l' hzero, perturb_difference l l' hzero⟩

/-- Relative to one compatible lift, perturbation by derivations parametrizes all compatible
lifts bijectively. -/
theorem perturbMap_bijective {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π) :
    Function.Bijective (l.perturbMap hzero) := by
  exact ⟨perturbMap_injective l hzero, perturbMap_surjective l hzero⟩

/-- Every compatible lift has a unique relative derivation as its difference from `l`. -/
theorem existsUnique_difference {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l l' : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π) :
    ∃! D : Der[α ; KernelIdeal.restrict π l.hom],
      IsDifference α π l.hom l'.hom D := by
  refine ⟨l.difference l' hzero, difference_spec l l' hzero, ?_⟩
  intro D hD
  exact ((difference_eq_iff l l' hzero D).mpr hD).symm

/-- Relative to `l`, perturbation and the canonical difference identify relative derivations
with all compatible lifts. -/
@[stacks 01UP "torsor chart", stacks 04BP "torsor chart"]
noncomputable def perturbEquiv {α : R ⟶ B} {β : R ⟶ A} {π : A ⟶ Q} {f : B ⟶ Q}
    (l : Lift α β π f) (hzero : KernelIdeal.IsSquareZero π) :
    Der[α ; KernelIdeal.restrict π l.hom] ≃ Lift α β π f where
  toFun := l.perturbMap hzero
  invFun := fun l' ↦ l.difference l' hzero
  left_inv := difference_perturb l hzero
  right_inv := fun l' ↦ perturb_difference l l' hzero

end Lift

/-- A compatible algebra section is a lift of the identity morphism through `π`. -/
abbrev IsSection (α : R ⟶ Q) (β : R ⟶ A) (π : A ⟶ Q) (s : Q ⟶ A) : Prop :=
  IsLift α β π (𝟙 Q) s

/-- The bundled type of compatible algebra sections of `π`. -/
@[stacks 04BP "compatible algebra sections", stacks 01UP "compatible algebra sections"]
abbrev Section (α : R ⟶ Q) (β : R ⟶ A) (π : A ⟶ Q) :=
  Lift α β π (𝟙 Q)

end SquareZeroExtension

-- The non-Prop payload of the following definitions is explicit. Any `sorryAx` is confined to
-- ring-homomorphism laws, restriction naturality, and bundled compatibility proofs.

-- The difference data is the canonical additive kernel lift; deferred debt is confined to the
-- vanishing, Leibniz, relative, and naturality laws.

-- The equivalence has explicit forward and inverse data; deferred debt is confined to its laws.

end SheafOfModules.RingedSite
