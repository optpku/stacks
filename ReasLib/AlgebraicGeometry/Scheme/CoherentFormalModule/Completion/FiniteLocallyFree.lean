/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Sections
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.FiniteLocallyFreeStage
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentCompletion

/-- The object property of coherent modules whose underlying module sheaf is finite locally free. -/
def finiteLocallyFree (X : Scheme.{u}) :
    ObjectProperty (RingedSpace.Coh X.toRingedSpace) :=
  fun E ↦ SheafOfModules.IsFiniteLocallyFree E.obj

/-- Membership in `finiteLocallyFree X` is exactly finite local freeness of the underlying
module sheaf. -/
theorem finiteLocallyFree_iff (X : Scheme.{u}) (E : RingedSpace.Coh X.toRingedSpace) :
    finiteLocallyFree X E ↔ SheafOfModules.IsFiniteLocallyFree E.obj := sorry

variable {X : Scheme.{u}} [IsNoetherian X]

/-- Coherent completion restricted to the full subcategory of finite locally free coherent
modules. -/
def onFiniteLocallyFree (I : X.IdealSheafData) :
    Functor (finiteLocallyFree X).FullSubcategory (CoherentFormalModules X I) :=
  (finiteLocallyFree X).ι ⋙ functor I

/-- The restricted completion functor agrees on objects with canonical coherent completion. -/
theorem onFiniteLocallyFree_obj (I : X.IdealSheafData)
    (E : (finiteLocallyFree X).FullSubcategory) :
    (onFiniteLocallyFree I).obj E = (functor I).obj E.obj := sorry

/-- Completions of finite locally free coherent sheaves remain finite locally free
as coherent formal modules. -/
theorem onFiniteLocallyFree_obj_isFiniteLocallyFree (I : X.IdealSheafData)
    (E : (finiteLocallyFree X).FullSubcategory) :
    CoherentFormalModules.finiteLocallyFree X I ((onFiniteLocallyFree I).obj E) := sorry

/-- Coherent completion as a functor between the finite locally free full
subcategories of coherent modules and of coherent formal modules. -/
noncomputable def onFiniteLocallyFreeToFiniteLocallyFree (I : X.IdealSheafData) :
    (finiteLocallyFree X).FullSubcategory ⥤
      (CoherentFormalModules.finiteLocallyFree X I).FullSubcategory :=
  (CoherentFormalModules.finiteLocallyFree X I).lift (onFiniteLocallyFree I)
    (onFiniteLocallyFree_obj_isFiniteLocallyFree I)

/-- The restricted completion functor agrees with `onFiniteLocallyFree` after
including into all coherent formal modules. -/
theorem onFiniteLocallyFreeToFiniteLocallyFree_comp_ι (I : X.IdealSheafData) :
    onFiniteLocallyFreeToFiniteLocallyFree I ⋙
        (CoherentFormalModules.finiteLocallyFree X I).ι =
      onFiniteLocallyFree I := sorry

/-- Quasi-affineness and structure-sheaf completeness imply eventual ample-power completeness. -/
theorem quasiAffine_implies_hasAmple (I : X.IdealSheafData)
    (hX : X.IsQuasiAffine)
    (h_complete : Function.Bijective
      (sectionsComparison I (SheafOfModules.unit X.ringCatSheaf))) :
    ∃ L : X.Modules, Modules.isAmpleObject L ∧
      ∃ m₀ : ℕ, ∀ m ≥ m₀,
        Function.Bijective
          (sectionsComparison I (RingedSpace.TensorPower.sheaf L m)) := sorry

/-- Eventual ample-power completeness implies completeness of every finite locally free coherent
module. -/
theorem hasAmple_implies_finiteLocallyFree (I : X.IdealSheafData) (L : X.Modules)
    (hL : Modules.isAmpleObject L)
    (h_complete : ∃ m₀ : ℕ, ∀ m ≥ m₀,
      Function.Bijective
        (sectionsComparison I (RingedSpace.TensorPower.sheaf L m))) :
    ∀ E : RingedSpace.Coh X.toRingedSpace, finiteLocallyFree X E →
      Function.Bijective (sectionsComparison I E.obj) := sorry

/-- Completeness of every finite locally free coherent module implies full faithfulness of
completion on that full subcategory. -/
theorem finiteLocallyFree_implies_fullyFaithful (I : X.IdealSheafData)
    (h_complete : ∀ E : RingedSpace.Coh X.toRingedSpace, finiteLocallyFree X E →
      Function.Bijective (sectionsComparison I E.obj)) :
    Nonempty (onFiniteLocallyFree I).FullyFaithful := sorry

/-- Full faithfulness of completion on finite locally free coherent modules implies completeness
of every such module. -/
theorem fullyFaithful_implies_finiteLocallyFree (I : X.IdealSheafData)
    (h_fully_faithful : Nonempty (onFiniteLocallyFree I).FullyFaithful) :
    ∀ E : RingedSpace.Coh X.toRingedSpace, finiteLocallyFree X E →
      Function.Bijective (sectionsComparison I E.obj) := sorry

end AlgebraicGeometry.Scheme.CoherentCompletion
