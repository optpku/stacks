/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Coherator
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.21.1: for a quasi-compact and quasi-separated scheme `X`, the inclusion
`D_QCoh(𝓞_X) ⟶ D(𝓞_X)` has a right adjoint. -/
@[stacks 0CR0] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.inclusionIsLeftAdjoint :
    ∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X],
      (inclusion X).IsLeftAdjoint)

end AlgebraicGeometry.Scheme.DerivedQCoh
