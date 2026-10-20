/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat.Resolution
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.23.7

The reusable owner gives a fixed-base-good source together with a DG-module quasi-isomorphism to
the prescribed module.  The statement uses the canonical morphism property `Module.quasiIso` and
does not assert goodness after arbitrary ringed-topos base change.
-/

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {O : Sheaf J CommRingCat.{w}} {A : DGA(O)}
variable (M : Mod(A, d))

/- Lemma 24.23.7 (0FSH), fixed-base form: every right DG module has a quasi-isomorphic
fixed-base-good resolution. -/
@[stacks 0FSH "fixed-base-good quasi-isomorphic resolution"]
#check
  (IsGoodAtBase.exists_quasiIso M :
    ∃ (P : Mod(A, d)) (π : P ⟶ M), Module.quasiIso A π ∧ IsGoodAtBase P)

/- The atomic quasi-isomorphism predicate used by the resolution theorem. -/
#check (Module.quasiIso A : MorphismProperty Mod(A, d))

end SheafOfModules.RingedSite.DifferentialGradedModule

end
