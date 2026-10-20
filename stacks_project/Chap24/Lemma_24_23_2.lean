module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat.Admissible
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.23.2

Admissibility is defined in the category of differential graded modules and forgets only the
differential, retaining the graded action of the coefficient algebra.  The three atomic
two-out-of-three statements below are the fixed-base component of the source lemma.  Universal
base-change stability is deliberately kept in the geometric `RingedSite.ToposHom` layer.
-/

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
variable (S : ShortComplex Mod(A, d)) (hS : IsAdmissibleShortExact S)

/- Lemma 24.23.2 (1), fixed-base component: goodness passes to an admissible quotient. -/
@[stacks 0FSC "(1), fixed-base admissible quotient"]
#check
  (IsGoodAtBase.of_left_middle S hS :
    IsGoodAtBase S.X₁ → IsGoodAtBase S.X₂ → IsGoodAtBase S.X₃)

/- Lemma 24.23.2 (2), fixed-base component: goodness is closed under admissible extensions. -/
@[stacks 0FSC "(2), fixed-base admissible extension"]
#check
  (IsGoodAtBase.of_left_right S hS :
    IsGoodAtBase S.X₁ → IsGoodAtBase S.X₃ → IsGoodAtBase S.X₂)

/- Lemma 24.23.2 (3), fixed-base component: goodness passes to an admissible kernel. -/
@[stacks 0FSC "(3), fixed-base admissible kernel"]
#check
  (IsGoodAtBase.of_middle_right S hS :
    IsGoodAtBase S.X₂ → IsGoodAtBase S.X₃ → IsGoodAtBase S.X₁)

/- The source-faithful admissibility predicate and its split-map characterization. -/
#check (IsAdmissibleShortExact S : Prop)
#check
  (isAdmissibleShortExact_iff S :
    IsAdmissibleShortExact S ↔
      S.ShortExact ∧
        IsSplitMono ((forgetToGraded A).map S.f) ∧
        IsSplitEpi ((forgetToGraded A).map S.g))

end SheafOfModules.RingedSite.DifferentialGradedModule

end
