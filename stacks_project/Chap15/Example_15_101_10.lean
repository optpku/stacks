/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Nodal

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open IadicFiniteModuleSystem.Ext

noncomputable section

universe u

/-!
Example 15.101.10: for `A = k[[x, y]] / (x * y)`, `I = (x)`, and
`M = N = A / (y)`, the ambient group `Ext²_A(M, N)` is linearly equivalent to `k`, while every
positive reduced group `Ext²_{A / I ^ n}(M / I ^ n M, N / I ^ n N)` vanishes.

The reusable objects, explicit resolution windows, and computation theorem are owned by
`IadicFiniteModuleSystem.Ext.Nodal`.

@stack 0EH2
-/

#check @Nodal.Ring
#check @Nodal.idealX
#check @Nodal.quotientModule
#check @Nodal.ambientProjectiveResolution
#check @Nodal.ambientHomExt2Window
#check @Nodal.ambientExtComputation
#check @Nodal.ambientExt2Window
@[stacks 0EH2 "explicit form of the ambient degree-two Hom window"]
#check @Nodal.ambientWindowIso
@[stacks 0EH2 "linear homology comparison for the ambient degree-two Hom window"]
#check @Nodal.ambientWindowHomologyEquiv
#check @Nodal.yTorsion_quotientModule_eq_top
#check @Nodal.stageResolutionAtTwo
#check @Nodal.stageExt2Window
#check @Nodal.stageNumerator_quotientModule_eq_torsion
#check @Nodal.stageExt2Window_quotientModule_exact
@[stacks 0EH2 "torsion quotient formula for the ambient second Ext group"]
#check @Nodal.ext2Formula
@[stacks 0EH2 "ambient second Ext group over the residue field"]
#check @Nodal.ext2EquivBase
@[stacks 0EH2 "Ext counterexample for the nodal ideal-power quotients"]
#check (Nodal.ext2Counterexample :
  ∀ (k : Type u) [Field k],
    Ext (Nodal.quotientModule k) (Nodal.quotientModule k) 2 ≃ₗ[k] k)

@[stacks 0EH2 "vanishing of the reduced Ext groups in the nodal counterexample"]
#check (Nodal.stageExt2IsZero :
  ∀ (k : Type u) [Field k] (n : ℕ+),
    IsZero
      (ModuleCat.of (Nodal.StageRing k n)
        (Ext (Nodal.stageModule k (Nodal.quotientModule k) n)
          (Nodal.stageModule k (Nodal.quotientModule k) n) 2)))
