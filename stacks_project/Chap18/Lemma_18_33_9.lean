/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension
public import Mathlib.Topology.Sheaves.CommRingCat
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped RelativeDerivation
open SheafOfModules.RingedSite

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {O₁ O₂ A : Sheaf J CommRingCat.{max u v}}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{max u v})]
variable (φ : O₁ ⟶ O₂) (ψ : O₁ ⟶ A) (π : A ⟶ O₂)

variable (s s' : SquareZeroExtension.Section φ ψ π)

/- Lemma 18.33.9 (04BP): relative to one compatible algebra section, perturbation identifies
relative derivations into the square-zero kernel ideal with all compatible algebra sections. -/
@[stacks 04BP]
#check (SquareZeroExtension.Lift.perturbEquiv s :
  ∀ _ : KernelIdeal.IsSquareZero π,
    Der[φ ; KernelIdeal.restrict π s.hom] ≃ SquareZeroExtension.Section φ ψ π)

/- The inverse chart chooses the unique difference derivation between two sections. -/
#check (SquareZeroExtension.Lift.difference s s' :
  ∀ _ : KernelIdeal.IsSquareZero π,
    Der[φ ; KernelIdeal.restrict π s.hom])

/- Its specification, uniqueness criterion, and inverse laws are available independently. -/
#check @SquareZeroExtension.Lift.difference_spec
#check @SquareZeroExtension.Lift.difference_eq_iff
#check @SquareZeroExtension.Lift.perturb_difference
#check @SquareZeroExtension.Lift.difference_perturb

end
