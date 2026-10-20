/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Injective
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology presheaves of modules on a ringed site

The primary objects are module-valued right derived functors of the canonical inclusion from
module sheaves to module presheaves.  Forgetting the module structure recovers the ordinary
cohomology presheaf of the underlying additive sheaf.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}

/-- The degree-`p` module-valued cohomology-presheaf functor on a ringed site. -/
@[stacks 06YK "module-valued cohomology presheaf functor"]
abbrev cohomologyPresheafFunctor (𝒪 : Sheaf J RingCat.{max u v}) (p : ℕ) :
    SheafOfModules 𝒪 ⥤ PresheafOfModules 𝒪.obj :=
  (forget 𝒪).rightDerived p

/-- The module-valued cohomology presheaf of one module sheaf. -/
abbrev cohomologyPresheaf
    (𝒪 : Sheaf J RingCat.{max u v}) (F : SheafOfModules 𝒪) (p : ℕ) :
    PresheafOfModules 𝒪.obj :=
  (cohomologyPresheafFunctor 𝒪 p).obj F

/-- Module cohomology evaluated at one object of the site, with its additive structure retained. -/
abbrev cohomologyAtObjectFunctor
    (𝒪 : Sheaf J RingCat.{max u v}) (p : ℕ) (U : C) :
    SheafOfModules 𝒪 ⥤ AddCommGrpCat.{max u v} :=
  cohomologyPresheafFunctor 𝒪 p ⋙
    PresheafOfModules.toPresheaf 𝒪.obj ⋙
      (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

section Comparison

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Forgetting the module structure on the derived module-inclusion functor recovers the
cohomology-presheaf functor of the underlying additive sheaf. -/
@[stacks 06YK "underlying additive cohomology presheaf"]
theorem cohomologyPresheafFunctor_toPresheaf_isomorphic
    (𝒪 : Sheaf J RingCat.{max u v}) (p : ℕ) :
    IsIsomorphic
      (((forget 𝒪).rightDerived p) ⋙ PresheafOfModules.toPresheaf 𝒪.obj)
      (toSheaf 𝒪 ⋙ Sheaf.cohomologyPresheafFunctor J p) := sorry

/-- For one module sheaf, forgetting its module-valued cohomology presheaf gives the
cohomology presheaf of its underlying additive sheaf. -/
theorem cohomologyPresheaf_toPresheaf_isomorphic
    (𝒪 : Sheaf J RingCat.{max u v}) (F : SheafOfModules 𝒪) (p : ℕ) :
    IsIsomorphic
      ((PresheafOfModules.toPresheaf 𝒪.obj).obj (cohomologyPresheaf 𝒪 F p))
      (((toSheaf 𝒪).obj F).cohomologyPresheaf p) := sorry

/-- Evaluating the underlying additive presheaf of module cohomology recovers objectwise
cohomology of the underlying additive sheaf. -/
theorem cohomologyAtObject_isomorphic
    (𝒪 : Sheaf J RingCat.{max u v}) (F : SheafOfModules 𝒪) (p : ℕ) (U : C) :
    IsIsomorphic
      ((cohomologyAtObjectFunctor 𝒪 p U).obj F)
      (((toSheaf 𝒪).obj F).H' p U) := sorry

/-- 21.2.0.5 (071G): cohomology over an object is computed by evaluating a chosen injective
resolution and taking the homology of the resulting sections complex. -/
@[stacks 071G "objectwise module cohomology from an injective resolution"]
theorem cohomologyAtObject_isomorphic_homology_of_injectiveResolution
    (𝒪 : Sheaf J RingCat.{max u v}) (F : SheafOfModules 𝒪)
    (I : InjectiveResolution F) (p : ℕ) (U : C) :
    IsIsomorphic ((cohomologyAtObjectFunctor 𝒪 p U).obj F)
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v}
        (ComplexShape.up ℕ) p).obj
          (((SheafOfModules.evaluation.{max u v} 𝒪 (op U) ⋙
            forget₂ (ModuleCat.{max u v} (𝒪.obj.obj (op U)))
              AddCommGrpCat.{max u v}).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj I.cocomplex)) := sorry

end Comparison

end SheafOfModules
