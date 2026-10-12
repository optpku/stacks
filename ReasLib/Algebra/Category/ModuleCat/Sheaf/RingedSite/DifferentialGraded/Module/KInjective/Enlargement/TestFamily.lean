/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.Enlargement
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.KInjective.TestFamily

/-!
# Enlargements attached to K-injective test families

This bridge specializes the general acyclic-enlargement existence theorem to the bundled test
family API, eliminating repeated source, target, arrow, monomorphism, and acyclicity arguments.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.Module.KInjective.TestFamily

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- A bundled combined test family admits a functorial acyclic enlargement. -/
theorem nonempty_enlargement {𝒜 : DGA(𝒪)}
    (T : TestFamily.{u, v, w} 𝒜) :
    Nonempty (AcyclicEnlargement 𝒜 T.source T.target T.ι) := sorry

end

end SheafOfModules.RingedSite.DifferentialGradedModule.Module.KInjective.TestFamily
