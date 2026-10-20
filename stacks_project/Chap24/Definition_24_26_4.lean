/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Derived.Basic
import StacksCheckRecall

/-!
# Definition 24.26.4

The derived category of DG module sheaves is the canonical Verdier quotient of the intrinsic DG
homotopy category by its acyclic objects.  The owner also exposes the localization functor.
-/

@[expose] public section

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}} (𝒜 : DGA(𝒪))

/- Definition 24.26.4 (1) (0FT5): the DG derived category is the Verdier quotient by acyclic
objects. -/
@[stacks 0FT5]
#check
  (DerivedCategory 𝒜 : Type (max (u + 1) (v + 1)))

/- Definition 24.26.4 (2) (0FT5): `Qh` is its canonical homotopy-category localization. -/
@[stacks 0FT5]
#check
  (DerivedCategory.Qh 𝒜 : K ℤ Mod(𝒜, d) ⥤ DerivedCategory 𝒜)

#check
  (inferInstance :
    (DerivedCategory.Qh 𝒜).IsLocalization (Homotopy.quasiIso 𝒜))

end SheafOfModules.RingedSite.DifferentialGradedModule
