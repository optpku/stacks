module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Iterated.ShortComplex
public import ReasLib.Algebra.Category.ModuleCat.ShortComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local splittings over locally finite-free retracts

An epimorphism of module sheaves whose target is locally a retract of a finite free module
becomes split after passing to a covering family.  Consequently, a short exact complex with
such a target is locally split.  The public surface records only the genuinely local existence;
restriction and the resulting splitting retain their canonical owners.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FiniteFreeRetract.IsLocal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, ∀ V : Over U,
  HasWeakSheafify ((J.over U).over V) AddCommGrpCat.{w}]
variable [∀ U : C, ∀ V : Over U,
  ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- An epimorphism onto a locally finite-free retract admits sections after restricting to a
cover of any object of the site. -/
@[stacks 0B38 "local sections of the quotient map"]
theorem existsCover_section {M N : SheafOfModules.{w} R}
    (f : M ⟶ N) [Epi f] [FiniteFreeRetract.IsLocal N] (U : C) :
    ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
      ∀ i : I,
        ∃ s : (N.over U).over (Ui i) ⟶ (M.over U).over (Ui i),
          s ≫ (f.over U).over (Ui i) = 𝟙 ((N.over U).over (Ui i)) := sorry

/-- A short exact complex whose target is locally a finite-free retract becomes split on a
cover after restriction to any object of the site. -/
@[stacks 0B38 "local splitting of a short exact complex"]
theorem existsCover_splittingOver
    {S : ShortComplex (SheafOfModules.{w} R)} (hS : S.ShortExact)
    [FiniteFreeRetract.IsLocal S.X₃] (U : C) :
    ∃ (I : Type (max u v)) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
      ∀ i : I,
        Nonempty
          (((S.map (SheafOfModules.Localization.restriction R U)).map
            (SheafOfModules.Localization.restriction (R.over U) (Ui i))).Splitting) := sorry

/-- A short exact complex whose target is locally a finite-free retract becomes split after
restriction to every member of a covering family of the original site. -/
@[stacks 0B38 "splitting cover of a short exact complex"]
theorem existsCover_splitting
    {S : ShortComplex (SheafOfModules.{w} R)} (hS : S.ShortExact)
    [FiniteFreeRetract.IsLocal S.X₃] :
    ∃ (I : Type (max u v)) (U : I → C), J.CoversTop U ∧
      ∀ i : I,
        Nonempty
          ((S.map (SheafOfModules.Localization.restriction R (U i))).Splitting) := sorry

end SheafOfModules.RingedSite.FiniteFreeRetract.IsLocal
