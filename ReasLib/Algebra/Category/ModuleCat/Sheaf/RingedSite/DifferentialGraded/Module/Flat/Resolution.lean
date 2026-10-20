module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.QuasiIso
public import ReasLib.Algebra.Homology.HomologicalComplex.HomologyMaps
public import ReasLib.Algebra.Homology.HomologicalComplex.MonoEpi
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-base-good resolutions of differential graded modules

This file records the two existence interfaces used by downstream constructions: a fixed-base-good
cover that is epimorphic both degreewise and on cycles, and a fixed-base-good quasi-isomorphic
resolution.  These statements deliberately do not claim goodness after arbitrary base change.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {𝒪 : Sheaf J CommRingCat.{w}} {A : DGA(𝒪)}

namespace IsGoodAtBase

/-- Lemma 24.23.4 (0FSE), fixed-base form: every right DG `A`-module admits a map from a
fixed-base-good module which is epimorphic degreewise and on cycles in every degree. -/
@[stacks 0FSE "fixed-base-good cover"]
theorem exists_cover (M : Mod(A, d)) :
    ∃ (P : Mod(A, d)) (π : P ⟶ M),
      Epi π.toCochainMap ∧ π.toCochainMap.EpiOnCycles ∧ IsGoodAtBase P := sorry

/-- Lemma 24.23.7 (0FSH), fixed-base form: every right DG `A`-module admits a DG-module
quasi-isomorphism from a fixed-base-good module. -/
@[stacks 0FSH "fixed-base-good quasi-isomorphic resolution"]
theorem exists_quasiIso (M : Mod(A, d)) :
    ∃ (P : Mod(A, d)) (π : P ⟶ M), Module.quasiIso A π ∧ IsGoodAtBase P := sorry

end IsGoodAtBase

end

end SheafOfModules.RingedSite.DifferentialGradedModule

end
