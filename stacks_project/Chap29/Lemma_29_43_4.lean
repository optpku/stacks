/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Cover
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.43.4: a morphism of schemes is locally projective if and only if it is H-projective
after restriction to every member of some open cover of the target. -/
@[stacks 01WB] #check
  (AlgebraicGeometry.locallyProjective_iff_exists_openCover_hProjective :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.LocallyProjective f ↔
        ∃ 𝒰 : AlgebraicGeometry.Scheme.OpenCover.{u} S,
          ∀ i : 𝒰.I₀,
            AlgebraicGeometry.HProjective (f ∣_ ((𝒰.f i).opensRange)))
