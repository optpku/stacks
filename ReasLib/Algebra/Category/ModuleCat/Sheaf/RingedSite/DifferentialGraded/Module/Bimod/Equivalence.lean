/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Bimod
public import ReasLib.CategoryTheory.Functor.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential graded modules and right module objects

The homogeneous and internal presentations of a right differential graded module contain the same
data.  This file extracts homogeneous action maps from a Mathlib right module object and packages
the two constructions as an equivalence of categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

/-- Extract the homogeneous right action from a right module object over `𝒢.toMon`. -/
@[stacks 0FSA "right module object as a differential graded module"]
noncomputable def ofBimod {𝒢 : DGA(𝒪)}
    (M : CategoryTheory.Bimod.RightModule 𝒢.toMon) : Mod(𝒢, d) where
  toComplex := M.X
  smul := HomologicalComplex.Monoidal.tensorHomComponent M.actRight
  smul_assoc := sorry
  one_smul := sorry
  d_smul := sorry

/-- A morphism of right module objects as a differential graded module morphism. -/
noncomputable def ofBimodMap {𝒢 : DGA(𝒪)}
    {M N : CategoryTheory.Bimod.RightModule 𝒢.toMon} (f : M ⟶ N) :
    ofBimod M ⟶ ofBimod N where
  toCochainMap := f.hom
  comm := by
    intro n m
    change HomologicalComplex.Monoidal.tensorHomComponent M.actRight n m ≫ f.hom.f (n + m) =
      (f.hom.f n ▷ 𝒢.toComplex.X m) ≫
        HomologicalComplex.Monoidal.tensorHomComponent N.actRight n m
    have h := congrArg
      (fun g ↦ HomologicalComplex.Monoidal.tensorHomComponent g n m) f.right_act_hom
    change HomologicalComplex.Monoidal.tensorHomComponent (M.actRight ≫ f.hom) n m =
      HomologicalComplex.Monoidal.tensorHomComponent
        (HomologicalComplex.tensorHom f.hom (𝟙 𝒢.toComplex) ≫ N.actRight) n m at h
    rw [HomologicalComplex.Monoidal.tensorHomComponent_comp M.actRight f.hom,
      HomologicalComplex.Monoidal.tensorHomComponent_tensorHom] at h
    simp only [HomologicalComplex.id_f, tensorHom_id] at h
    exact h

/-- The functor extracting differential graded modules from right module objects. -/
@[stacks 0FSA "right module object extraction functor"]
noncomputable def ofBimodFunctor (𝒢 : DGA(𝒪)) :
    CategoryTheory.Bimod.RightModule 𝒢.toMon ⥤ Mod(𝒢, d) where
  obj := ofBimod
  map := ofBimodMap
  map_id := by
    intro X
    apply Hom.ext
    rfl
  map_comp := by
    intro X Y Z f g
    apply Hom.ext
    rfl

/-- The extracted differential graded module has the original underlying cochain complex. -/
@[simp]
theorem ofBimod_toComplex {𝒢 : DGA(𝒪)}
    (M : CategoryTheory.Bimod.RightModule 𝒢.toMon) :
    (ofBimod M).toComplex = M.X := rfl

/-- The extracted action is the restriction of the internal right action to degrees `(n, m)`. -/
@[simp]
theorem ofBimod_smul {𝒢 : DGA(𝒪)}
    (M : CategoryTheory.Bimod.RightModule 𝒢.toMon) (n m : ℤ) :
    (ofBimod M).smul n m =
      HomologicalComplex.Monoidal.tensorHomComponent M.actRight n m := rfl

/-- Extraction preserves the underlying cochain map of a right module morphism. -/
@[simp]
theorem ofBimodMap_toCochainMap {𝒢 : DGA(𝒪)}
    {M N : CategoryTheory.Bimod.RightModule 𝒢.toMon} (f : M ⟶ N) :
    (ofBimodMap f).toCochainMap = f.hom := rfl

/-- Extracting homogeneous components after assembling a DG module recovers its original action. -/
@[simp]
theorem ofBimod_toBimod_smul {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) (n m : ℤ) :
    (ofBimod (toBimod M)).smul n m = M.smul n m := by
  change CategoryTheory.GradedObject.Monoidal.ιTensorObj
      M.toComplex.X 𝒢.toComplex.X n m (n + m) rfl ≫
      CategoryTheory.GradedObject.Monoidal.actionHom
        M.toComplex.X 𝒢.toComplex.X M.smul (n + m) = M.smul n m
  simp only [CategoryTheory.GradedObject.Monoidal.actionHom,
    CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc, eqToHom_refl, Category.comp_id]

/-- Reassembling an extracted right module recovers its internal right action. -/
@[simp]
theorem toBimod_ofBimod_actRight {𝒢 : DGA(𝒪)}
    (M : CategoryTheory.Bimod.RightModule 𝒢.toMon) :
    (toBimod (ofBimod M)).actRight = M.actRight := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro n m h
  subst k
  change CategoryTheory.GradedObject.Monoidal.ιTensorObj
      M.X.X 𝒢.toComplex.X n m (n + m) rfl ≫
      CategoryTheory.GradedObject.Monoidal.actionHom
        M.X.X 𝒢.toComplex.X (ofBimod M).smul (n + m) = _
  simp only [CategoryTheory.GradedObject.Monoidal.actionHom,
    CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc, eqToHom_refl,
    Category.comp_id]
  rfl

/-- The objectwise unit comparison for the DG-module/right-module equivalence. -/
noncomputable def toBimodUnitIsoApp {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) :
    M ≅ ofBimod (toBimod M) where
  hom :=
    { toCochainMap := 𝟙 M.toComplex
      comm := by
        intro n m
        change M.smul n m ≫ 𝟙 _ = (𝟙 _ ▷ 𝒢.toComplex.X m) ≫
          (ofBimod (toBimod M)).smul n m
        rw [Category.comp_id, id_whiskerRight, Category.id_comp]
        exact (ofBimod_toBimod_smul M n m).symm }
  inv :=
    { toCochainMap := 𝟙 M.toComplex
      comm := by
        intro n m
        change (ofBimod (toBimod M)).smul n m ≫ 𝟙 _ =
          (𝟙 _ ▷ 𝒢.toComplex.X m) ≫ M.smul n m
        rw [Category.comp_id, id_whiskerRight, Category.id_comp]
        exact ofBimod_toBimod_smul M n m }
  hom_inv_id := by
    apply Hom.ext
    change (𝟙 M.toComplex) ≫ 𝟙 M.toComplex = 𝟙 M.toComplex
    simp only [Category.id_comp]
  inv_hom_id := by
    apply Hom.ext
    change (𝟙 M.toComplex) ≫ 𝟙 M.toComplex = 𝟙 M.toComplex
    simp only [Category.id_comp]

/-- The unit comparison is the identity on underlying cochain complexes. -/
@[simp]
theorem toBimodUnitIsoApp_hom {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) :
    (toBimodUnitIsoApp M).hom.toCochainMap = 𝟙 M.toComplex := by
  change 𝟙 M.toComplex = 𝟙 M.toComplex
  rfl

/-- The objectwise counit comparison for the DG-module/right-module equivalence. -/
noncomputable def toBimodCounitIsoApp {𝒢 : DGA(𝒪)}
    (M : CategoryTheory.Bimod.RightModule 𝒢.toMon) :
    toBimod (ofBimod M) ≅ M :=
  Bimod.isoOfIso (Iso.refl M.X)
    (by
      change (λ_ M.X).hom ≫ 𝟙 _ = (_ ◁ 𝟙 M.X) ≫ M.actLeft
      rw [Category.comp_id, whiskerLeft_id, Category.id_comp]
      have h := M.one_actLeft
      change (𝟙 _ ▷ M.X) ≫ M.actLeft = (λ_ M.X).hom at h
      rw [id_whiskerRight, Category.id_comp] at h
      exact h.symm)
    (by
      change (toBimod (ofBimod M)).actRight ≫ 𝟙 _ = (𝟙 M.X ▷ _) ≫ M.actRight
      rw [Category.comp_id, id_whiskerRight, Category.id_comp]
      exact toBimod_ofBimod_actRight M)

/-- The counit comparison is the identity on underlying cochain complexes. -/
@[simp]
theorem toBimodCounitIsoApp_hom {𝒢 : DGA(𝒪)}
    (M : CategoryTheory.Bimod.RightModule 𝒢.toMon) :
    (toBimodCounitIsoApp M).hom.hom = 𝟙 M.X := by
  change 𝟙 M.X = 𝟙 M.X
  rfl

/-- The natural unit for the DG-module/right-module equivalence. -/
noncomputable def toBimodUnitIso (𝒢 : DGA(𝒪)) :
    𝟭 Mod(𝒢, d) ≅ toBimodFunctor 𝒢 ⋙ ofBimodFunctor 𝒢 :=
  NatIso.ofComponents (fun M ↦ toBimodUnitIsoApp M) (by
    intro M N f
    apply Hom.ext
    change f.toCochainMap ≫ 𝟙 _ = 𝟙 _ ≫ f.toCochainMap
    simp only [Category.comp_id, Category.id_comp])

/-- The natural counit for the DG-module/right-module equivalence. -/
noncomputable def toBimodCounitIso (𝒢 : DGA(𝒪)) :
    ofBimodFunctor 𝒢 ⋙ toBimodFunctor 𝒢 ≅
      𝟭 (CategoryTheory.Bimod.RightModule 𝒢.toMon) :=
  NatIso.ofComponents (fun M ↦ toBimodCounitIsoApp M) (by
    intro M N f
    apply Bimod.Hom.ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp only [Category.comp_id, Category.id_comp])

/-- Explicit quasi-inverse data for the DG-module/right-module bridge. -/
@[stacks 0FSA "differential graded module right module quasi-inverse"]
noncomputable def toBimodQuasiInverse (𝒢 : DGA(𝒪)) :
    CategoryTheory.Functor.QuasiInverse (toBimodFunctor 𝒢) where
  inverse := ofBimodFunctor 𝒢
  unitIso := toBimodUnitIso 𝒢
  counitIso := toBimodCounitIso 𝒢

/-- Differential graded right modules are equivalent to Mathlib right module objects over the
associated monoid object. -/
@[stacks 0FSA "differential graded modules as right module objects"]
noncomputable def toBimodEquivalence (𝒢 : DGA(𝒪)) :
    Mod(𝒢, d) ≌ CategoryTheory.Bimod.RightModule 𝒢.toMon :=
  (toBimodQuasiInverse 𝒢).adjointifyUnit

/-- The forward functor of `toBimodEquivalence` is the canonical assembly functor. -/
@[simp]
theorem toBimodEquivalence_functor (𝒢 : DGA(𝒪)) :
    (toBimodEquivalence 𝒢).functor = toBimodFunctor 𝒢 := rfl

/-- The inverse functor of `toBimodEquivalence` extracts homogeneous action maps. -/
@[simp]
theorem toBimodEquivalence_inverse (𝒢 : DGA(𝒪)) :
    (toBimodEquivalence 𝒢).inverse = ofBimodFunctor 𝒢 := rfl

/-- The canonical assembly functor from right DG modules to right module objects is an
equivalence. -/
@[stacks 0FSA "right DG module assembly functor equivalence"]
instance toBimodFunctor_isEquivalence (𝒢 : DGA(𝒪)) :
    (toBimodFunctor 𝒢).IsEquivalence :=
  (toBimodQuasiInverse 𝒢).isEquivalence

/-- The functor extracting a right DG module from a right module object is an equivalence. -/
@[stacks 0FSA "right DG module extraction functor equivalence"]
instance ofBimodFunctor_isEquivalence (𝒢 : DGA(𝒪)) :
    (ofBimodFunctor 𝒢).IsEquivalence := by
  exact (toBimodQuasiInverse 𝒢).symm.isEquivalence

end

end SheafOfModules.RingedSite.DifferentialGradedModule

end
