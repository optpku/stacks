/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
  comm := sorry

/-- The functor extracting differential graded modules from right module objects. -/
@[stacks 0FSA "right module object extraction functor"]
noncomputable def ofBimodFunctor (𝒢 : DGA(𝒪)) :
    CategoryTheory.Bimod.RightModule 𝒢.toMon ⥤ Mod(𝒢, d) where
  obj := ofBimod
  map := ofBimodMap
  map_id := sorry
  map_comp := sorry

/-- The extracted differential graded module has the original underlying cochain complex. -/
@[simp]
theorem ofBimod_toComplex {𝒢 : DGA(𝒪)}
    (M : CategoryTheory.Bimod.RightModule 𝒢.toMon) :
    (ofBimod M).toComplex = M.X := sorry

/-- The extracted action is the restriction of the internal right action to degrees `(n, m)`. -/
@[simp]
theorem ofBimod_smul {𝒢 : DGA(𝒪)}
    (M : CategoryTheory.Bimod.RightModule 𝒢.toMon) (n m : ℤ) :
    (ofBimod M).smul n m =
      HomologicalComplex.Monoidal.tensorHomComponent M.actRight n m := sorry

/-- Extraction preserves the underlying cochain map of a right module morphism. -/
@[simp]
theorem ofBimodMap_toCochainMap {𝒢 : DGA(𝒪)}
    {M N : CategoryTheory.Bimod.RightModule 𝒢.toMon} (f : M ⟶ N) :
    (ofBimodMap f).toCochainMap = f.hom := sorry

/-- Extracting homogeneous components after assembling a DG module recovers its original action. -/
@[simp]
theorem ofBimod_toBimod_smul {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) (n m : ℤ) :
    (ofBimod (toBimod M)).smul n m = M.smul n m := sorry

/-- Reassembling an extracted right module recovers its internal right action. -/
@[simp]
theorem toBimod_ofBimod_actRight {𝒢 : DGA(𝒪)}
    (M : CategoryTheory.Bimod.RightModule 𝒢.toMon) :
    (toBimod (ofBimod M)).actRight = M.actRight := sorry

/-- The objectwise unit comparison for the DG-module/right-module equivalence. -/
noncomputable def toBimodUnitIsoApp {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) :
    M ≅ ofBimod (toBimod M) where
  hom :=
    { toCochainMap := 𝟙 M.toComplex
      comm := sorry }
  inv :=
    { toCochainMap := 𝟙 M.toComplex
      comm := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The unit comparison is the identity on underlying cochain complexes. -/
@[simp]
theorem toBimodUnitIsoApp_hom {𝒢 : DGA(𝒪)} (M : Mod(𝒢, d)) :
    (toBimodUnitIsoApp M).hom.toCochainMap = 𝟙 M.toComplex := sorry

/-- The objectwise counit comparison for the DG-module/right-module equivalence. -/
noncomputable def toBimodCounitIsoApp {𝒢 : DGA(𝒪)}
    (M : CategoryTheory.Bimod.RightModule 𝒢.toMon) :
    toBimod (ofBimod M) ≅ M :=
  Bimod.isoOfIso (Iso.refl M.X) sorry sorry

/-- The counit comparison is the identity on underlying cochain complexes. -/
@[simp]
theorem toBimodCounitIsoApp_hom {𝒢 : DGA(𝒪)}
    (M : CategoryTheory.Bimod.RightModule 𝒢.toMon) :
    (toBimodCounitIsoApp M).hom.hom = 𝟙 M.X := sorry

/-- The natural unit for the DG-module/right-module equivalence. -/
noncomputable def toBimodUnitIso (𝒢 : DGA(𝒪)) :
    𝟭 Mod(𝒢, d) ≅ toBimodFunctor 𝒢 ⋙ ofBimodFunctor 𝒢 :=
  NatIso.ofComponents (fun M ↦ toBimodUnitIsoApp M) (fun _ ↦ sorry)

/-- The natural counit for the DG-module/right-module equivalence. -/
noncomputable def toBimodCounitIso (𝒢 : DGA(𝒪)) :
    ofBimodFunctor 𝒢 ⋙ toBimodFunctor 𝒢 ≅
      𝟭 (CategoryTheory.Bimod.RightModule 𝒢.toMon) :=
  NatIso.ofComponents (fun M ↦ toBimodCounitIsoApp M) (fun _ ↦ sorry)

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
    (toBimodEquivalence 𝒢).functor = toBimodFunctor 𝒢 := sorry

/-- The inverse functor of `toBimodEquivalence` extracts homogeneous action maps. -/
@[simp]
theorem toBimodEquivalence_inverse (𝒢 : DGA(𝒪)) :
    (toBimodEquivalence 𝒢).inverse = ofBimodFunctor 𝒢 := sorry

/-- The canonical assembly functor from right DG modules to right module objects is an
equivalence. -/
@[stacks 0FSA "right DG module assembly functor equivalence"]
instance toBimodFunctor_isEquivalence (𝒢 : DGA(𝒪)) :
    (toBimodFunctor 𝒢).IsEquivalence := sorry

/-- The functor extracting a right DG module from a right module object is an equivalence. -/
@[stacks 0FSA "right DG module extraction functor equivalence"]
instance ofBimodFunctor_isEquivalence (𝒢 : DGA(𝒪)) :
    (ofBimodFunctor 𝒢).IsEquivalence := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule

end
