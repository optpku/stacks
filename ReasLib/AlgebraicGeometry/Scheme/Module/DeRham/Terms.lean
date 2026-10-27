/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeZero
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.DegreeOne
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationMonoidal

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace AlgebraicGeometry.Scheme.Modules.DeRham

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))

/-- Actual relative differential sheaf on Y, defined by the sheafified
universal relative derivation, rather than differentials of Γ(Y). -/
noncomputable abbrev oneForms : Y.Modules :=
  RingedSpace.Hom.differentials f.toShHom

/-- Exterior powers are formed in module sheaves by sheafification. -/
noncomputable def forms (n : ℕ) : Y.Modules :=
  SheafOfModules.RingedSite.ExteriorPower.sheaf Y.sheaf (oneForms f) n

/-- The genuine sheaf tensor product. Both exterior power and tensor
construction include sheafification; no raw presheaf tensor is declared
to be a sheaf on all nonaffine opens. -/
noncomputable def term (M : Y.Modules) (n : ℕ) : Y.Modules :=
  SheafOfModules.RingedSite.moduleTensor (𝒪 := Y.sheaf) M (forms f n)

/-- The coefficient tensored with the actual sheaf of relative one-forms. -/
noncomputable def oneFormTensor (M : Y.Modules) : Y.Modules :=
  SheafOfModules.RingedSite.moduleTensor (𝒪 := Y.sheaf) M (oneForms f)

/-- Retain every local section and restriction map while viewing an
O_Y-module as a sheaf of A-modules through the specified structure map. -/
noncomputable def asBaseSheaf (M : Y.Modules) : TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat :=
  (sheafCompose (Opens.grothendieckTopology Y.toTopCat)
    (ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap f))).obj
      ((SheafOfModules.forgetToSheafModuleCat Y.ringCatSheaf (op ⊤)
        (initialOpOfTerminal isTerminalTop)).obj M)

/-- The actual de Rham term as an A-module sheaf; this is the appropriate
ambient category for a connection differential, which need not be O_Y-linear. -/
noncomputable def baseTerm (M : Y.Modules) (n : ℕ) : TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat :=
  asBaseSheaf f (term f M n)

end AlgebraicGeometry.Scheme.Modules.DeRham

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
namespace AlgebraicGeometry.Scheme.Modules.DeRham

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
variable (M : Y.Modules)

/-- Restriction of scalars as an actual functor on all local sections. -/
noncomputable def baseFunctor : Y.Modules ⥤ TopCat.Sheaf (ModuleCat.{u} A) Y.toTopCat :=
  SheafOfModules.forgetToSheafModuleCat Y.ringCatSheaf (op ⊤)
      (initialOpOfTerminal isTerminalTop) ⋙
    sheafCompose (Opens.grothendieckTopology Y.toTopCat)
      (ModuleCat.restrictScalars (Scheme.Hom.globalSectionsMap f))

/-- Tensoring a genuine sheaf with the structure module is canonically
the sheaf itself, using the actual sheafification tensor comparison. -/
noncomputable def tensorStructureIso : moduleTensor (𝒪 := Y.sheaf) M (unitModule _ Y.sheaf) ≅ M :=
  ModuleSheafification.tensorObjIso Y.sheaf M (unitModule _ Y.sheaf) ≪≫
    (moduleSheafification Y.sheaf).mapIso (ρ_ M.val) ≪≫
      moduleSheafificationValIso Y.sheaf M

/-- The zero-degree sheaf term is canonically the original coefficient
sheaf; both arrows are fixed by exterior degree zero and tensor-unit maps. -/
noncomputable def degreeZero : term f M 0 ≅ M :=
  tensorIso (Iso.refl M)
      (SheafOfModules.RingedSite.ExteriorPower.degreeZeroIso Y.sheaf
        (oneForms f)) ≪≫
    tensorStructureIso M

/-- The first-degree term is canonically the coefficient tensor the
actual relative differential sheaf. -/
noncomputable def degreeOne : term f M 1 ≅
    moduleTensor (𝒪 := Y.sheaf) M (oneForms f) :=
  tensorIso (Iso.refl M)
    (SheafOfModules.RingedSite.ExteriorPower.degreeOneIso Y.sheaf
      (oneForms f)).symm

/-- Degree zero remains the same coefficient after restricting scalars to A. -/
noncomputable def baseDegreeZero : baseTerm f M 0 ≅
    asBaseSheaf f M :=
  (baseFunctor f).mapIso (degreeZero f M)

/-- The connection target remains the genuine sheaf tensor after
restricting scalars, rather than a tensor of nonaffine global sections. -/
noncomputable def baseDegreeOne : baseTerm f M 1 ≅
    asBaseSheaf f
      (moduleTensor (𝒪 := Y.sheaf) M (oneForms f)) :=
  (baseFunctor f).mapIso (degreeOne f M)

end AlgebraicGeometry.Scheme.Modules.DeRham
