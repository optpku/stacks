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

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CrystallineSmoothLiftTerms

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

end CrystallineSmoothLiftTerms
