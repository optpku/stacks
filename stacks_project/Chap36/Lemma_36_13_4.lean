/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Ext
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.13.4: for a bounded complex with quasi-coherent cohomology on a
quasi-compact and quasi-separated scheme, Ext from any finite locally free module vanishes
in all sufficiently large degrees. -/
@[stacks 08EF] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.extSubsingletonEventually :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (E : Bounded X),
      ∃ n₀ : ℤ, 0 < n₀ ∧
        ∀ (F : X.Modules) [F.IsFiniteLocallyFree] (n : ℤ), n₀ ≤ n →
          Subsingleton
            (Ext⁽n⁾((DerivedCategory.singleFunctor X.toRingedSpace.Modules 0).obj F,
              DerivedCategory.Bounded.ι.obj E.obj)))

end AlgebraicGeometry.Scheme.DerivedQCoh
