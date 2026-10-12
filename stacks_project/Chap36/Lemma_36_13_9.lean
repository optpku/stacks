/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Support
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 36.13.9: on a quasi-compact quasi-separated scheme, a morphism from a perfect
object of `D_QCoh(𝒪_X)` to one supported on `X.zeroLocus {f}` is annihilated by a power
of the global section `f`. -/
@[stacks 08EJ] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_pow_smul_eq_zero :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (f : Γ(X, ⊤))
      {E E' : DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)}
      (α : E ⟶ E'),
      RingedSpace.ModuleDerived.IsPerfect E.obj →
        RingedSpace.ModuleDerived.IsSupportedOn E'.obj (X.zeroLocus {f}) →
          ∃ n : ℕ, (f ^ n) • α = 0)
