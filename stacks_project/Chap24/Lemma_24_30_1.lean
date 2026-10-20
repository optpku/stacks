/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.ChangeOfRings.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DifferentialGradedModule.ChangeOfRings.Derived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {A B : DGA(𝒪)} (f : A ⟶ B)
variable (hf : DifferentialGradedAlgebra.quasiIso f)

/- Lemma 24.30.1 (tag 0FTZ): derived extension of scalars along a quasi-isomorphism of
differential graded algebra sheaves is an equivalence. -/
@[stacks 0FTZ]
#check (extension_isEquivalence f hf : (extension f).IsEquivalence)

/- The same change-of-rings API supplies the quasi-inverse-side equivalence property. -/
#check (restriction_isEquivalence f hf : (restriction f).IsEquivalence)

/- Derived extension and restriction retain their canonical adjunction independently of the
quasi-isomorphism hypothesis. -/
#check (adjunction f : extension f ⊣ restriction f)

end SheafOfModules.RingedSite.DifferentialGradedModule.ChangeOfRings.Derived
