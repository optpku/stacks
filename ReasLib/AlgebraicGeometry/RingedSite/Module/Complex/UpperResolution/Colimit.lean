/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.UpperResolution.Colimit
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Upper-Truncation Resolution Colimits on Ringed Sites

This file specializes the property-neutral upper-resolution colimit criterion
to modules over a commutative ring sheaf.  The specialization is isolated from
the algebraic tower API and relies only on the Grothendieck-category
infrastructure for module sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CochainComplex.UpperTruncation.Resolution

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
  (𝒪 : Sheaf J CommRingCat.{max u v})
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- For modules on a ringed site, the canonical map from the sequential
colimit of an upper-truncation resolution to its target is a
quasi-isomorphism. -/
theorem fromColimit_quasiIso_of_ringedSite
    {P : ObjectProperty (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪)}
    {K : CochainComplex
      (SheafOfModules.RingedSite.ringedSiteModuleCategory J 𝒪) ℤ}
    (S : UpperTruncation.Resolution P K) : QuasiIso S.fromColimit := sorry

end CochainComplex.UpperTruncation.Resolution
