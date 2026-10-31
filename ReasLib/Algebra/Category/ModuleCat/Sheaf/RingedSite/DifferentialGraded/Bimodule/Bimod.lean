/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Bimodule
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Bimod
public import ReasLib.CategoryTheory.GradedObject.Monoidal.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential graded bimodule sheaves as bimodule objects

A differential graded `(A, B)`-bimodule sheaf canonically determines a bimodule object between
the monoid objects associated to `A` and `B` in the category of cochain complexes.  This is the
common bridge through which relative tensor products and relative internal Homs reuse Mathlib's
generic bimodule API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.DifferentialGradedBimodule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedBimodule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Assemble the homogeneous left action of a differential graded bimodule into a morphism of
cochain complexes. -/
@[stacks 0FRS "differential graded bimodule left action"]
noncomputable def leftActionHom {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) :
    HomologicalComplex.tensorObj 𝒜.toComplex N.toComplex ⟶ N.toComplex where
  f n := CategoryTheory.GradedObject.Monoidal.leftActionHom
    𝒜.toComplex.X N.toComplex.X N.leftMul n
  comm' := by
    intro p q hpq
    change p + 1 = q at hpq
    subst q
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro n m h
    change n + m = p at h
    subst p
    change HomologicalComplex.ιTensorObj 𝒜.toComplex N.toComplex n m (n + m) rfl ≫
        (HomologicalComplex.mapBifunctorDesc
          (K₁ := 𝒜.toComplex) (K₂ := N.toComplex)
          (F := curriedTensor (ringedSiteModuleCategory J 𝒪)) (c := up ℤ)
          (fun i j h ↦ N.leftMul i j ≫ eqToHom (congrArg N.toComplex.X h)) ≫
          N.toComplex.d (n + m) (n + m + 1)) =
      HomologicalComplex.ιTensorObj 𝒜.toComplex N.toComplex n m (n + m) rfl ≫
        ((HomologicalComplex.tensorObj 𝒜.toComplex N.toComplex).d (n + m) (n + m + 1) ≫
          HomologicalComplex.mapBifunctorDesc
            (K₁ := 𝒜.toComplex) (K₂ := N.toComplex)
            (F := curriedTensor (ringedSiteModuleCategory J 𝒪)) (c := up ℤ)
            (fun i j h ↦ N.leftMul i j ≫ eqToHom (congrArg N.toComplex.X h)))
    simp only [HomologicalComplex.ι_mapBifunctorDesc_assoc,
      eqToHom_refl, Category.id_comp, HomologicalComplex.mapBifunctor.d_eq,
      Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc,
      HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (by rfl) m _
        (add_right_comm n 1 m),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ n (by rfl) _
        (add_assoc n m 1).symm]
    simp only [Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    change N.leftMul n m ≫ N.toComplex.d (n + m) (n + m + 1) =
      (1 : ℤˣ) • ((𝒜.toComplex.d n (n + 1)) ▷ N.toComplex.X m) ≫
          N.leftMul (n + 1) m ≫
          eqToHom (congrArg N.toComplex.X (add_right_comm n 1 m)) +
        n.negOnePow • (𝒜.toComplex.X n ◁ N.toComplex.d m (m + 1)) ≫
          N.leftMul n (m + 1) ≫
          eqToHom (congrArg N.toComplex.X (Int.add_assoc n m 1).symm)
    simpa only [one_smul, Linear.units_smul_comp, Category.assoc] using N.d_leftMul n m

/-- Extracting a homogeneous component of the assembled left action recovers the original
degreewise left action. -/
@[simp]
theorem leftActionHom_component {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) (n m : ℤ) :
    HomologicalComplex.Monoidal.tensorHomComponent (leftActionHom N) n m =
      N.leftMul n m := by
  change CategoryTheory.GradedObject.Monoidal.ιTensorObj 𝒜.toComplex.X N.toComplex.X
      n m (n + m) rfl ≫
    CategoryTheory.GradedObject.Monoidal.tensorObjDesc
      (fun i j h ↦ N.leftMul i j ≫ eqToHom (congrArg N.toComplex.X h)) = _
  simp only [CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc,
    eqToHom_refl, Category.comp_id]

private theorem right_component {A : DGA(𝒪)} (M : Mod(A, d)) (i j : ℤ) :
    HomologicalComplex.Monoidal.tensorHomComponent
      (DifferentialGradedModule.actionHom M) i j = M.smul i j := by
  change CategoryTheory.GradedObject.Monoidal.ιTensorObj M.toComplex.X A.toComplex.X
      i j (i + j) rfl ≫
    CategoryTheory.GradedObject.Monoidal.tensorObjDesc
      (fun p q h ↦ M.smul p q ≫ eqToHom (congrArg M.toComplex.X h)) = _
  simp only [CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc,
    eqToHom_refl, Category.comp_id]

private theorem mul_component (A : DGA(𝒪)) (i j : ℤ) :
    HomologicalComplex.Monoidal.tensorHomComponent
      (DifferentialGradedAlgebra.mulHom A) i j = A.mul i j := by
  change CategoryTheory.GradedObject.Monoidal.ιTensorObj A.toComplex.X A.toComplex.X
      i j (i + j) rfl ≫
    CategoryTheory.GradedObject.Monoidal.tensorObjDesc
      (fun p q h ↦ A.mul p q ≫ eqToHom (congrArg A.toComplex.X h)) = _
  simp only [CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc,
    eqToHom_refl, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem unit_component (A : DGA(𝒪)) : HomologicalComplex.Monoidal.unitHomComponent
    (DifferentialGradedAlgebra.oneHom A) = A.one := by
  change (HomologicalComplex.singleObjXSelf (up ℤ) 0
      (𝟙_ (ringedSiteModuleCategory J 𝒪))).inv ≫
    (((HomologicalComplex.singleObjXSelf (up ℤ) 0
        (𝟙_ (ringedSiteModuleCategory J 𝒪))).hom ≫
      (CategoryTheory.GradedObject.singleObjApplyIsoOfEq 0
        (𝟙_ (ringedSiteModuleCategory J 𝒪)) 0 rfl).inv) ≫
      ((CategoryTheory.GradedObject.singleObjApplyIsoOfEq 0
        (𝟙_ (ringedSiteModuleCategory J 𝒪)) 0 rfl).hom ≫ A.one)) = A.one
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem tensor_component
    {K L M : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    (f : HomologicalComplex.tensorObj K L ⟶ M) (i j t : ℤ) (h : i + j = t) :
    CategoryTheory.GradedObject.Monoidal.ιTensorObj K.X L.X i j t h ≫ f.f t =
      HomologicalComplex.Monoidal.tensorHomComponent f i j ≫
        eqToHom (congrArg M.X h) := by
  subst t
  simp only [eqToHom_refl, Category.comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem assoc_of_components
    {K L M P Q T : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    (f : HomologicalComplex.tensorObj K L ⟶ P)
    (g : HomologicalComplex.tensorObj P M ⟶ T)
    (h : HomologicalComplex.tensorObj L M ⟶ Q)
    (k : HomologicalComplex.tensorObj K Q ⟶ T)
    (comm : ∀ i j n : ℤ,
      (α_ (K.X i) (L.X j) (M.X n)).hom ≫
          (K.X i ◁ HomologicalComplex.Monoidal.tensorHomComponent h j n) ≫
          HomologicalComplex.Monoidal.tensorHomComponent k i (j + n) =
        (HomologicalComplex.Monoidal.tensorHomComponent f i j ▷ M.X n) ≫
          HomologicalComplex.Monoidal.tensorHomComponent g (i + j) n ≫
          eqToHom (congrArg T.X (Int.add_assoc i j n))) :
    (f ▷ M) ≫ g = (α_ K L M).hom ≫ (K ◁ h) ≫ k := by
  apply HomologicalComplex.Hom.ext
  funext t
  apply CategoryTheory.GradedObject.Monoidal.tensorObj₃'_ext
  intro i j n ht
  subst t
  change CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'
      K.X L.X M.X i j n (i + j + n) rfl ≫
      (CategoryTheory.GradedObject.Monoidal.tensorHom f.f (𝟙 M.X) (i + j + n) ≫
        g.f (i + j + n)) =
    CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'
      K.X L.X M.X i j n (i + j + n) rfl ≫
      ((CategoryTheory.GradedObject.Monoidal.associator K.X L.X M.X).hom (i + j + n) ≫
        CategoryTheory.GradedObject.Monoidal.tensorHom (𝟙 K.X) h.f (i + j + n) ≫
          k.f (i + j + n))
  rw [CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_associator_hom_assoc]
  simp only [CategoryTheory.GradedObject.Monoidal.ιTensorObj₃',
    CategoryTheory.GradedObject.Monoidal.ιTensorObj₃, Category.assoc,
    CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc, tensor_component,
    eqToHom_refl, Category.comp_id]
  change (CategoryTheory.GradedObject.Monoidal.ιTensorObj K.X L.X i j (i + j) rfl ▷ M.X n) ≫
      (f.f (i + j) ⊗ₘ 𝟙 (M.X n)) ≫
        HomologicalComplex.Monoidal.tensorHomComponent g (i + j) n =
    (α_ (K.X i) (L.X j) (M.X n)).hom ≫
      (K.X i ◁ CategoryTheory.GradedObject.Monoidal.ιTensorObj L.X M.X j n (j + n) rfl) ≫
      (𝟙 (K.X i) ⊗ₘ h.f (j + n)) ≫
        HomologicalComplex.Monoidal.tensorHomComponent k i (j + n) ≫
          eqToHom (congrArg T.X (Int.add_assoc i j n).symm)
  simp only [tensorHom_id, id_tensorHom,
    ← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc]
  change (HomologicalComplex.Monoidal.tensorHomComponent f i j ▷ M.X n) ≫
      HomologicalComplex.Monoidal.tensorHomComponent g (i + j) n =
    (α_ (K.X i) (L.X j) (M.X n)).hom ≫
      (K.X i ◁ HomologicalComplex.Monoidal.tensorHomComponent h j n) ≫
      HomologicalComplex.Monoidal.tensorHomComponent k i (j + n) ≫
        eqToHom (congrArg T.X (Int.add_assoc i j n).symm)
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
    congrArg (fun p ↦ p ≫ eqToHom (congrArg T.X (Int.add_assoc i j n).symm))
      (comm i j n).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A differential graded `(A, B)`-bimodule sheaf as a bimodule object between the associated
cochain-complex monoids. -/
@[stacks 0FRS "differential graded bimodule as a bimodule object"]
noncomputable def toBimod {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) :
    Bimod 𝒜.toMon 𝒝.toMon where
  X := N.toComplex
  actLeft := leftActionHom N
  actRight := DifferentialGradedModule.actionHom N.toRightModule
  one_actLeft := by
    apply (cancel_epi (λ_ N.toComplex).inv).1
    rw [Iso.inv_hom_id]
    apply HomologicalComplex.Hom.ext
    funext n
    change (HomologicalComplex.leftUnitor' N.toComplex).inv n ≫
        (CategoryTheory.GradedObject.Monoidal.tensorHom
          (DifferentialGradedAlgebra.oneHom 𝒜).f (𝟙 _) n ≫
          (leftActionHom N).f n) = 𝟙 _
    rw [HomologicalComplex.leftUnitor'_inv]
    change (λ_ (N.toComplex.X n)).inv ≫
        ((HomologicalComplex.singleObjXSelf (up ℤ) 0
          (𝟙_ (ringedSiteModuleCategory J 𝒪))).inv ▷ N.toComplex.X n) ≫
          CategoryTheory.GradedObject.Monoidal.ιTensorObj
            (HomologicalComplex.tensorUnit (ringedSiteModuleCategory J 𝒪) (up ℤ)).X
            N.toComplex.X 0 n n (zero_add n) ≫
            CategoryTheory.GradedObject.Monoidal.tensorHom
              (DifferentialGradedAlgebra.oneHom 𝒜).f (𝟙 N.toComplex.X) n ≫
              CategoryTheory.GradedObject.Monoidal.tensorObjDesc
                (fun i j h ↦ N.leftMul i j ≫ eqToHom (congrArg N.toComplex.X h)) = 𝟙 _
    simp only [CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc,
      CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc]
    change (λ_ (N.toComplex.X n)).inv ≫
        ((HomologicalComplex.singleObjXSelf (up ℤ) 0
          (𝟙_ (ringedSiteModuleCategory J 𝒪))).inv ▷ N.toComplex.X n) ≫
          ((DifferentialGradedAlgebra.oneHom 𝒜).f 0 ⊗ₘ 𝟙 (N.toComplex.X n)) ≫
            N.leftMul 0 n ≫ eqToHom (congrArg N.toComplex.X (zero_add n)) = 𝟙 _
    rw [tensorHom_id, ← comp_whiskerRight_assoc]
    change (λ_ (N.toComplex.X n)).inv ≫
        (HomologicalComplex.Monoidal.unitHomComponent (DifferentialGradedAlgebra.oneHom 𝒜) ▷
          N.toComplex.X n) ≫ N.leftMul 0 n ≫
          eqToHom (congrArg N.toComplex.X (zero_add n)) = 𝟙 _
    rw [unit_component 𝒜, ← N.one_left n, Iso.inv_hom_id]
  left_assoc := by
    apply assoc_of_components (DifferentialGradedAlgebra.mulHom 𝒜)
      (leftActionHom N) (leftActionHom N) (leftActionHom N)
    intro i j k
    simpa only [mul_component, leftActionHom_component] using N.left_assoc i j k
  actRight_one := by
    apply (cancel_epi (ρ_ N.toComplex).inv).1
    rw [Iso.inv_hom_id]
    apply HomologicalComplex.Hom.ext
    funext n
    change (HomologicalComplex.rightUnitor' N.toComplex).inv n ≫
        (CategoryTheory.GradedObject.Monoidal.tensorHom (𝟙 _)
          (DifferentialGradedAlgebra.oneHom 𝒝).f n ≫
          (DifferentialGradedModule.actionHom N.toRightModule).f n) = 𝟙 _
    rw [HomologicalComplex.rightUnitor'_inv]
    change (ρ_ (N.toComplex.X n)).inv ≫
        (N.toComplex.X n ◁ (HomologicalComplex.singleObjXSelf (up ℤ) 0
          (𝟙_ (ringedSiteModuleCategory J 𝒪))).inv) ≫
          CategoryTheory.GradedObject.Monoidal.ιTensorObj N.toComplex.X
            (HomologicalComplex.tensorUnit (ringedSiteModuleCategory J 𝒪) (up ℤ)).X
            n 0 n (add_zero n) ≫
            CategoryTheory.GradedObject.Monoidal.tensorHom (𝟙 N.toComplex.X)
              (DifferentialGradedAlgebra.oneHom 𝒝).f n ≫
              CategoryTheory.GradedObject.Monoidal.tensorObjDesc
                (fun i j h ↦ N.toRightModule.smul i j ≫
                  eqToHom (congrArg N.toComplex.X h)) = 𝟙 _
    simp only [CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc,
      CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc]
    change (ρ_ (N.toComplex.X n)).inv ≫
        (N.toComplex.X n ◁ (HomologicalComplex.singleObjXSelf (up ℤ) 0
          (𝟙_ (ringedSiteModuleCategory J 𝒪))).inv) ≫
          (𝟙 (N.toComplex.X n) ⊗ₘ (DifferentialGradedAlgebra.oneHom 𝒝).f 0) ≫
            N.toRightModule.smul n 0 ≫
              eqToHom (congrArg N.toComplex.X (add_zero n)) = 𝟙 _
    rw [id_tensorHom, ← whiskerLeft_comp_assoc]
    change (ρ_ (N.toComplex.X n)).inv ≫
        (N.toComplex.X n ◁ HomologicalComplex.Monoidal.unitHomComponent
          (DifferentialGradedAlgebra.oneHom 𝒝)) ≫ N.toRightModule.smul n 0 ≫
          eqToHom (congrArg N.toComplex.X (add_zero n)) = 𝟙 _
    rw [unit_component 𝒝, ← N.toRightModule.one_smul n, Iso.inv_hom_id]
  right_assoc := by
    change (N.toComplex ◁ DifferentialGradedAlgebra.mulHom 𝒝) ≫
        DifferentialGradedModule.actionHom N.toRightModule =
      (α_ N.toComplex 𝒝.toComplex 𝒝.toComplex).inv ≫
        (DifferentialGradedModule.actionHom N.toRightModule ▷ 𝒝.toComplex) ≫
          DifferentialGradedModule.actionHom N.toRightModule
    apply (cancel_epi (α_ N.toComplex 𝒝.toComplex 𝒝.toComplex).hom).1
    simp only [Iso.hom_inv_id_assoc]
    symm
    apply assoc_of_components (DifferentialGradedModule.actionHom N.toRightModule)
      (DifferentialGradedModule.actionHom N.toRightModule)
      (DifferentialGradedAlgebra.mulHom 𝒝)
      (DifferentialGradedModule.actionHom N.toRightModule)
    intro i j k
    simpa only [right_component, mul_component] using N.toRightModule.smul_assoc i j k
  middle_assoc := by
    apply assoc_of_components (leftActionHom N)
      (DifferentialGradedModule.actionHom N.toRightModule)
      (DifferentialGradedModule.actionHom N.toRightModule) (leftActionHom N)
    intro i j k
    simpa only [leftActionHom_component, right_component] using N.middle_assoc i j k

/-- A differential graded bimodule map as a morphism between the associated bimodule objects. -/
noncomputable def toBimodMap {𝒜 𝒝 : DGA(𝒪)} {N N' : Mod(𝒜, 𝒝, d)} (f : N ⟶ N') :
    toBimod N ⟶ toBimod N' where
  hom := f.toRightHom.toCochainMap
  left_act_hom := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    subst k
    change CategoryTheory.GradedObject.Monoidal.ιTensorObj
        𝒜.toComplex.X N.toComplex.X i j (i + j) rfl ≫
        (CategoryTheory.GradedObject.Monoidal.leftActionHom
          𝒜.toComplex.X N.toComplex.X N.leftMul (i + j) ≫
          f.toRightHom.toCochainMap.f (i + j)) =
      CategoryTheory.GradedObject.Monoidal.ιTensorObj
        𝒜.toComplex.X N.toComplex.X i j (i + j) rfl ≫
        (CategoryTheory.GradedObject.Monoidal.tensorHom
          (𝟙 𝒜.toComplex.X) f.toRightHom.toCochainMap.f (i + j) ≫
          CategoryTheory.GradedObject.Monoidal.leftActionHom
            𝒜.toComplex.X N'.toComplex.X N'.leftMul (i + j))
    simp only [CategoryTheory.GradedObject.Monoidal.leftActionHom,
      CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc,
      CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc_assoc,
      CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc,
      eqToHom_refl, Category.comp_id]
    change N.leftMul i j ≫ f.toRightHom.toCochainMap.f (i + j) =
      (𝟙 (𝒜.toComplex.X i) ⊗ₘ f.toRightHom.toCochainMap.f j) ≫ N'.leftMul i j
    simpa only [id_tensorHom] using f.comm_leftMul i j
  right_act_hom := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    subst k
    change CategoryTheory.GradedObject.Monoidal.ιTensorObj
        N.toComplex.X 𝒝.toComplex.X i j (i + j) rfl ≫
        (CategoryTheory.GradedObject.Monoidal.actionHom
          N.toComplex.X 𝒝.toComplex.X N.toRightModule.smul (i + j) ≫
          f.toRightHom.toCochainMap.f (i + j)) =
      CategoryTheory.GradedObject.Monoidal.ιTensorObj
        N.toComplex.X 𝒝.toComplex.X i j (i + j) rfl ≫
        (CategoryTheory.GradedObject.Monoidal.tensorHom
          f.toRightHom.toCochainMap.f (𝟙 𝒝.toComplex.X) (i + j) ≫
          CategoryTheory.GradedObject.Monoidal.actionHom
            N'.toComplex.X 𝒝.toComplex.X N'.toRightModule.smul (i + j))
    simp only [CategoryTheory.GradedObject.Monoidal.actionHom,
      CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc,
      CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc_assoc,
      CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc,
      eqToHom_refl, Category.comp_id]
    change N.toRightModule.smul i j ≫ f.toRightHom.toCochainMap.f (i + j) =
      (f.toRightHom.toCochainMap.f i ⊗ₘ 𝟙 (𝒝.toComplex.X j)) ≫ N'.toRightModule.smul i j
    simpa only [tensorHom_id] using f.toRightHom.comm i j

/-- The canonical functor from differential graded bimodule sheaves to bimodule objects. -/
@[stacks 0FRS "differential graded bimodule object functor"]
noncomputable def toBimodFunctor (𝒜 𝒝 : DGA(𝒪)) :
    Mod(𝒜, 𝒝, d) ⥤ Bimod 𝒜.toMon 𝒝.toMon where
  obj := toBimod
  map := toBimodMap
  map_id _ := Bimod.hom_ext _ _ rfl
  map_comp _ _ := Bimod.hom_ext _ _ rfl

/-- The underlying cochain complex of the bimodule object associated to `N` is `N.toComplex`. -/
@[simp]
theorem toBimod_X {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) :
    (toBimod N).X = N.toComplex := rfl

/-- The assembled left action is the left action of the associated bimodule object. -/
@[simp]
theorem toBimod_actLeft {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) :
    (toBimod N).actLeft = leftActionHom N := rfl

/-- The assembled right action is the right action of the associated bimodule object. -/
@[simp]
theorem toBimod_actRight {𝒜 𝒝 : DGA(𝒪)} (N : Mod(𝒜, 𝒝, d)) :
    (toBimod N).actRight = DifferentialGradedModule.actionHom N.toRightModule := rfl

/-- The bimodule-object bridge sends a DG bimodule map to its underlying cochain map. -/
@[simp]
theorem toBimodMap_hom {𝒜 𝒝 : DGA(𝒪)} {N N' : Mod(𝒜, 𝒝, d)}
    (f : N ⟶ N') :
    (toBimodMap f).hom = f.toRightHom.toCochainMap := rfl

end

end SheafOfModules.RingedSite.DifferentialGradedBimodule

end
