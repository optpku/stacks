module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Limits

/-!
# Grothendieck structure on differential graded modules

This leaf owns the separator theorem and the resulting Grothendieck-abelian instance for
differential graded module sheaves over a fixed differential graded algebra.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

namespace DifferentialGradedModule

/-- Lemma 24.22.6 (0FS9): differential graded modules over `𝒜` have a separator. -/
@[stacks 0FS9 "separator"]
theorem hasSeparator (𝒜 : DGA(𝒪)) :
    HasSeparator (Mod(𝒜, d)) := sorry

/-- Lemma 24.22.6 (0FS9): differential graded modules over `𝒜` form a Grothendieck abelian
category. -/
@[stacks 0FS9 "Grothendieck abelian category"]
instance instIsGrothendieckAbelian (𝒜 : DGA(𝒪)) :
    IsGrothendieckAbelian.{max u v w} (Mod(𝒜, d)) := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
