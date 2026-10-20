/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension
import StacksCheckRecall

@[expose] public section

/-!
Lemma 17.28.11 (01UP): compatible splittings of a square-zero extension form a torsor under
relative derivations into its kernel ideal.  The ReasLib owner is formulated for commutative-ring
sheaves on an arbitrary site; the statement for ringed spaces is its opens-site specialization.
-/

/- Lemma 17.28.11 (01UP): relative to one compatible algebra section, perturbation explicitly
identifies relative derivations into the square-zero kernel ideal with all compatible sections. -/
@[stacks 01UP]
#check @SheafOfModules.RingedSite.SquareZeroExtension.Lift.perturbEquiv

/- The reusable data owner constructs a perturbed lift explicitly as `l + D`. -/
#check @SheafOfModules.RingedSite.SquareZeroExtension.perturb

/- Its public specifications record the local formula, compatibility, and difference relation. -/
#check @SheafOfModules.RingedSite.SquareZeroExtension.perturb_apply
#check @SheafOfModules.RingedSite.SquareZeroExtension.perturb_isLift
#check @SheafOfModules.RingedSite.SquareZeroExtension.perturb_isDifference

/- The inverse chart is a named difference derivation with a specification and uniqueness API. -/
#check @SheafOfModules.RingedSite.SquareZeroExtension.Lift.difference
#check @SheafOfModules.RingedSite.SquareZeroExtension.Lift.difference_spec
#check @SheafOfModules.RingedSite.SquareZeroExtension.Lift.difference_eq_iff

/- The two inverse laws expose the torsor chart without unpacking `Equiv`. -/
#check @SheafOfModules.RingedSite.SquareZeroExtension.Lift.perturb_difference
#check @SheafOfModules.RingedSite.SquareZeroExtension.Lift.difference_perturb

#check @SheafOfModules.RingedSite.KernelIdeal.IsSquareZero
#check @SheafOfModules.RingedSite.KernelIdeal.restrict
#check @SheafOfModules.RingedSite.SquareZeroExtension.IsLift
#check @SheafOfModules.RingedSite.SquareZeroExtension.IsDifference
