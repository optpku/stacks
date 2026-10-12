/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Exact
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.Colimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential colimits of K-flat complexes on a ringed site

This file exposes the ringed-site specialization of the exact-colimit API for K-flat cochain
complexes.  Exactness and tensor-colimit compatibility belong to the ambient module-sheaf
category and do not appear as source-facing hypotheses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.CochainComplex.IsKFlat

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Lemma 21.17.9: the sequential colimit of K-flat cochain complexes of modules on a ringed
site is K-flat. -/
@[stacks 06YR]
theorem sequentialColimit
    (F : ℕ ⥤ CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)
    (hF : ∀ i, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := sorry

end

end SheafOfModules.RingedSite.CochainComplex.IsKFlat
