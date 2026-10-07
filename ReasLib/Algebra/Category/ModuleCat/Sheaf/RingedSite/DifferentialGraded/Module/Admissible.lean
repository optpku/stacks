module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Forget
public import ReasLib.CategoryTheory.ShortComplex.Admissible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Admissible short exact sequences of differential graded modules

The differential is forgotten while the graded action of the differential graded algebra is
retained.  This is the source-faithful exact structure used by constructions on DG modules.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}} {A : DGA(O)}

/-- A short exact sequence of right DG `A`-modules is admissible when it splits after forgetting
the differential while retaining the graded `A`-action. -/
@[stacks 0FSC "admissible short exact sequence of differential graded modules"]
abbrev IsAdmissibleShortExact (S : ShortComplex Mod(A, d)) : Prop :=
  _root_.IsAdmissibleShortExact (forgetToGraded A) S

/-- DG-module admissibility is short exactness together with splitness of both maps in the category
of graded modules over the same algebra. -/
theorem isAdmissibleShortExact_iff (S : ShortComplex Mod(A, d)) :
    IsAdmissibleShortExact S ↔
      S.ShortExact ∧
        IsSplitMono ((forgetToGraded A).map S.f) ∧
        IsSplitEpi ((forgetToGraded A).map S.g) := sorry

end SheafOfModules.RingedSite.DifferentialGradedModule

end
