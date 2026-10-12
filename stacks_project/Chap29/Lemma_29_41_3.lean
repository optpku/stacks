/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.41.3: a morphism of schemes is proper if and only if there exists an open covering of
the target such that each restricted morphism over a member of the cover is proper. -/
@[stacks 01W2] #check
  (AlgebraicGeometry.IsZariskiLocalAtTarget.iff_exists_openCover
      (P := @AlgebraicGeometry.IsProper) :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      IsProper f ↔
        ∃ 𝒰 : S.OpenCover.{u}, ∀ i : 𝒰.I₀, IsProper (f ∣_ ((𝒰.f i).opensRange)))
