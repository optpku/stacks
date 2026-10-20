/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.Proper

/-!
# Completion of coherent modules with proper support

This file restricts coherent completion to coherent modules with proper support and coherent
formal modules whose first stage has proper support.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/-- The full category of coherent modules on `X` whose support is proper over `f : X ⟶ S`. -/
abbrev CoherentProperSupportOver (f : X ⟶ S) :=
  ObjectProperty.FullSubcategory
    ((fun ℱ : RingedSpace.Coh X.toRingedSpace ↦ HasProperSupportOver f ℱ.obj) :
      ObjectProperty (RingedSpace.Coh X.toRingedSpace))

/-- A coherent module in `CoherentProperSupportOver f` has proper support over `f`. -/
@[stacks 088D "proper-support coherent-module projection"]
theorem coherentProperSupportOver_obj_property (f : X ⟶ S)
    (ℱ : CoherentProperSupportOver f) :
    HasProperSupportOver f ℱ.obj.obj := sorry

/-- The stage indexed by `n` of a coherent formal module. -/
abbrev coherentFormalModuleStage
    {I : X.IdealSheafData} (M : Scheme.CoherentFormalModules X I) (n : ℕ) :
    RingedSpace.Coh X.toRingedSpace :=
  M.obj.obj (op n)

/-- The full category of coherent formal modules whose first stage has proper support over `f`. -/
abbrev CoherentFormalProperSupportOver (f : X ⟶ S) (I : X.IdealSheafData) :=
  ObjectProperty.FullSubcategory
    ((fun M : Scheme.CoherentFormalModules X I ↦
        HasProperSupportOver f (coherentFormalModuleStage M 1).obj) :
      ObjectProperty (Scheme.CoherentFormalModules X I))

/-- The first stage of an object of `CoherentFormalProperSupportOver f I` has proper support over
`f`. -/
@[stacks 088D "proper-support coherent-formal-module projection"]
theorem coherentFormalProperSupportOver_obj_property (f : X ⟶ S) (I : X.IdealSheafData)
    (M : CoherentFormalProperSupportOver f I) :
    HasProperSupportOver f (coherentFormalModuleStage M.obj 1).obj := sorry

/-- Canonical completion preserves proper support at the first coherent stage. -/
@[stacks 088D "canonical completion preserves proper support"]
theorem coherentCompletion_preservesProperSupportOver
    {f : X ⟶ S} [IsNoetherian X] [LocallyOfFiniteType f] {I : X.IdealSheafData}
    (ℱ : CoherentProperSupportOver f) :
    HasProperSupportOver f
      (coherentFormalModuleStage ((Scheme.CoherentCompletion.functor I).obj ℱ.obj) 1).obj := sorry

/-- Canonical completion restricted from coherent modules with proper support
to coherent formal modules whose first stage has proper support. -/
@[stacks 088D "canonical proper-support completion functor"]
noncomputable def coherentProperSupportCompletionFunctor
    {f : X ⟶ S} {I : X.IdealSheafData} [IsNoetherian X] [LocallyOfFiniteType f] :
    CoherentProperSupportOver f ⥤ CoherentFormalProperSupportOver f I :=
  ObjectProperty.lift
    ((fun M : Scheme.CoherentFormalModules X I ↦
        HasProperSupportOver f (coherentFormalModuleStage M 1).obj) :
      ObjectProperty (Scheme.CoherentFormalModules X I))
    (ObjectProperty.ι
      ((fun ℱ : RingedSpace.Coh X.toRingedSpace ↦ HasProperSupportOver f ℱ.obj) :
        ObjectProperty (RingedSpace.Coh X.toRingedSpace)) ⋙ Scheme.CoherentCompletion.functor I)
    coherentCompletion_preservesProperSupportOver

/-- Over an ideal-adically complete Noetherian ring, canonical completion on a separated
finite-type scheme is an equivalence from coherent modules with proper support to coherent
formal modules whose first stage has proper support. -/
@[stacks 088E, instance]
instance instIsEquivalence_coherentProperSupportCompletionFunctor
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsNoetherian X] (I : Ideal A) [IsAdicComplete I A]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [Scheme.Hom.FiniteType f] :
    (coherentProperSupportCompletionFunctor :
      CoherentProperSupportOver f ⥤
        CoherentFormalProperSupportOver f ((idealSheafDataOfIdealOnSpec I).comap f)).IsEquivalence :=
  sorry

end AlgebraicGeometry.Scheme.Modules
