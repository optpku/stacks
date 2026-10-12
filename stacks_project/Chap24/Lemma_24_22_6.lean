/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Grothendieck
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.22.6

The Grothendieck-abelian instance for differential graded module sheaves is owned by
`DifferentialGraded.Grothendieck`.
-/

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

/- Lemma 24.22.6 (0FS9): differential graded modules over a differential graded algebra on a
ringed site form a Grothendieck abelian category. -/
@[stacks 0FS9]
#check @DifferentialGradedModule.instIsGrothendieckAbelian
#check @DifferentialGradedModule.hasSeparator

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}
variable (𝒜 : DGA(𝒪))

#synth IsGrothendieckAbelian.{max u v w} (Mod(𝒜, d))
#synth HasSeparator (Mod(𝒜, d))

end

end SheafOfModules.RingedSite
