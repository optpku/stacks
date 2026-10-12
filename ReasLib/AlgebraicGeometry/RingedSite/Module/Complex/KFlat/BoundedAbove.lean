/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.BoundedAbove
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-above K-flat complexes on a ringed site

This file gives the ringed-site specialization of the categorical bounded-above criterion.  Its
public statement contains only the boundedness and termwise-flatness conditions from the source.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.CochainComplex.IsTermwiseFlat

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Lemma 21.17.8: a bounded-above termwise-flat cochain complex of modules on a ringed site is
K-flat. -/
@[stacks 06YQ]
theorem isKFlat_of_boundedAbove
    {K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ}
    (hFlat : HomologicalComplex.IsTermwiseFlat K)
    (hbounded : CochainComplex.minus (ringedSiteModuleCategory J 𝒪) K) :
    K.IsKFlat := sorry

end

end SheafOfModules.RingedSite.CochainComplex.IsTermwiseFlat
