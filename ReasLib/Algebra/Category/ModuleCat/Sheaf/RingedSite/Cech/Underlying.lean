/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology
public import ReasLib.CategoryTheory.Sites.Cech.Basic
public import ReasLib.CategoryTheory.Sites.Cech.Coefficients
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying additive ringed-site Cech complexes

This file identifies a module-valued Cech complex on a slice site, after forgetting the module
structure over the ring of sections of the covered object, with the ordinary additive Cech complex
of the restricted underlying presheaf.  The comparison is natural in the module presheaf and is
independent of ringed-space or chapter-specific constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.Cech.Underlying

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat) (U : C)

/-- Pointwise forgetting from presheaves of modules over `𝒪(U)` to additive presheaves. -/
abbrev pointwiseForget :
    ((Over U)ᵒᵖ ⥤ ModuleCat.{w} (𝒪.obj.obj (op U))) ⥤
      ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  (Functor.whiskeringRight (Over U)ᵒᵖ
    (ModuleCat.{w} (𝒪.obj.obj (op U))) AddCommGrpCat.{w}).obj
      (forget₂ (ModuleCat.{w} (𝒪.obj.obj (op U))) AddCommGrpCat.{w})

/-- Restricting scalars to `𝒪(U)` and then forgetting them leaves the underlying additive
presheaf unchanged. -/
@[stacks 01EI "forget restricted section scalars"]
noncomputable def forgetSectionsIso :
    PresheafOfModules.forgetToPresheafModuleCat
        (op (Over.mk (𝟙 U))) (SheafOfModules.RingedSite.overInitial U) ⋙
        pointwiseForget 𝒪 U ≅
      PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ 𝒪.obj) :=
  Iso.refl _

/-- Forgetting scalar structure on slice sections canonically gives the restriction of the
underlying additive presheaf to the slice. -/
@[stacks 01EI "underlying additive sections on a slice"]
noncomputable def sectionsIso :
    SheafOfModules.RingedSite.sectionsOnOver 𝒪 U ⋙ pointwiseForget 𝒪 U ≅
      PresheafOfModules.toPresheaf 𝒪.obj ⋙ restrictPresheafToOver U :=
  Functor.associator
      (PresheafOfModules.pushforward₀ (Over.forget U) 𝒪.obj)
      (PresheafOfModules.forgetToPresheafModuleCat
        (op (Over.mk (𝟙 U))) (SheafOfModules.RingedSite.overInitial U))
      (pointwiseForget 𝒪 U) ≪≫
    Functor.isoWhiskerLeft
      (PresheafOfModules.pushforward₀ (Over.forget U) 𝒪.obj)
      (forgetSectionsIso 𝒪 U) ≪≫
    PresheafOfModules.pushforward₀CompToPresheaf (Over.forget U) 𝒪.obj

variable [HasFiniteProducts (Over U)] {ι : Type w} (family : ι → Over U)

/-- The module-valued slice Cech complex after forgetting the `𝒪(U)`-module structure. -/
abbrev complexSource :
    PresheafOfModules.{w} 𝒪.obj ⥤ CochainComplex AddCommGrpCat.{w} ℕ :=
  SheafOfModules.RingedSite.cechComplex 𝒪 U family ⋙
    (forget₂ (ModuleCat.{w} (𝒪.obj.obj (op U))) AddCommGrpCat.{w}).mapHomologicalComplex
      (ComplexShape.up ℕ)

/-- The ordinary additive Cech complex of the underlying presheaf restricted to the slice. -/
abbrev complexTarget :
    PresheafOfModules.{w} 𝒪.obj ⥤ CochainComplex AddCommGrpCat.{w} ℕ :=
  PresheafOfModules.toPresheaf 𝒪.obj ⋙
    restrictPresheafToOver U ⋙ cechComplexFunctor family

/-- Forgetting the section-module structure on a ringed-site Cech complex canonically recovers
the additive Cech complex of the restricted underlying presheaf. -/
@[stacks 01EI "underlying additive ringed-site Cech complex"]
noncomputable def complexIso :
    complexSource 𝒪 U family ≅ complexTarget 𝒪 U family :=
  Functor.associator
      (SheafOfModules.RingedSite.sectionsOnOver 𝒪 U)
      (cechComplexFunctor family)
      ((forget₂ (ModuleCat.{w} (𝒪.obj.obj (op U)))
        AddCommGrpCat.{w}).mapHomologicalComplex (ComplexShape.up ℕ)) ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.RingedSite.sectionsOnOver 𝒪 U)
      (CategoryTheory.Cech.Coefficients.complexIso
        (forget₂ (ModuleCat.{w} (𝒪.obj.obj (op U))) AddCommGrpCat.{w}) family) ≪≫
    (Functor.associator
      (SheafOfModules.RingedSite.sectionsOnOver 𝒪 U)
      (pointwiseForget 𝒪 U) (cechComplexFunctor family)).symm ≪≫
    Functor.isoWhiskerRight (sectionsIso 𝒪 U) (cechComplexFunctor family) ≪≫
    Functor.associator
      (PresheafOfModules.toPresheaf 𝒪.obj)
      (restrictPresheafToOver U) (cechComplexFunctor family)

/-- The comparison on the degree-`p` Cech cohomology of one module presheaf. -/
@[stacks 01EI "underlying additive ringed-site Cech cohomology object"]
noncomputable def homologyAppIso
    (M : PresheafOfModules.{w} 𝒪.obj) (p : ℕ) :
    (forget₂ (ModuleCat.{w} (𝒪.obj.obj (op U))) AddCommGrpCat.{w}).obj
        ((HomologicalComplex.homologyFunctor
          (ModuleCat.{w} (𝒪.obj.obj (op U))) (ComplexShape.up ℕ) p).obj
          ((SheafOfModules.RingedSite.cechComplex 𝒪 U family).obj M)) ≅
      (HomologicalComplex.homologyFunctor
        AddCommGrpCat.{w} (ComplexShape.up ℕ) p).obj
        ((complexTarget 𝒪 U family).obj M) :=
  (HomologicalComplex.mapHomologyFunctorIso
      (forget₂ (ModuleCat.{w} (𝒪.obj.obj (op U))) AddCommGrpCat.{w}) p).symm.app
        ((SheafOfModules.RingedSite.cechComplex 𝒪 U family).obj M) ≪≫
    (HomologicalComplex.homologyFunctor
      AddCommGrpCat.{w} (ComplexShape.up ℕ) p).mapIso
        ((complexIso 𝒪 U family).app M)

/-- The objectwise underlying Cech-cohomology comparisons are natural in the module presheaf. -/
@[stacks 01EI "naturality of underlying ringed-site Cech cohomology"]
theorem homologyAppIso_hom_naturality
    {M N : PresheafOfModules.{w} 𝒪.obj} (f : M ⟶ N) (p : ℕ) :
    (SheafOfModules.RingedSite.cechComplex 𝒪 U family ⋙
      HomologicalComplex.homologyFunctor
        (ModuleCat.{w} (𝒪.obj.obj (op U))) (ComplexShape.up ℕ) p ⋙
      forget₂ (ModuleCat.{w} (𝒪.obj.obj (op U))) AddCommGrpCat.{w}).map f ≫
        (homologyAppIso 𝒪 U family N p).hom =
      (homologyAppIso 𝒪 U family M p).hom ≫
        (complexTarget 𝒪 U family ⋙
          HomologicalComplex.homologyFunctor
            AddCommGrpCat.{w} (ComplexShape.up ℕ) p).map f := sorry

/-- Forgetting the module structure on ringed-site Cech cohomology canonically recovers additive
Cech cohomology of the restricted underlying presheaf. -/
@[stacks 01EI "underlying additive ringed-site Cech cohomology"]
noncomputable def homologyIso (p : ℕ) :
    SheafOfModules.RingedSite.cechComplex 𝒪 U family ⋙
        HomologicalComplex.homologyFunctor
          (ModuleCat.{w} (𝒪.obj.obj (op U))) (ComplexShape.up ℕ) p ⋙
        forget₂ (ModuleCat.{w} (𝒪.obj.obj (op U))) AddCommGrpCat.{w} ≅
      complexTarget 𝒪 U family ⋙
        HomologicalComplex.homologyFunctor
          AddCommGrpCat.{w} (ComplexShape.up ℕ) p :=
  NatIso.ofComponents (fun M ↦ homologyAppIso 𝒪 U family M p)
    (fun f ↦ homologyAppIso_hom_naturality 𝒪 U family f p)

end SheafOfModules.RingedSite.Cech.Underlying
