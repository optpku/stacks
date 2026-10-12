/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap75.Lemma_75_20_3_Diagram

/-!
# Étale-local characterizations of Tor independence

Lemma 75.20.3 records that Tor independence of algebraic spaces over a common base
is equivalent to the corresponding condition on every étale vertical diagram, on
some étale-surjective covering diagram, and on some representable scheme covering
diagram using scheme-level Tor independence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentOver

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- Lemma 75.20.3: let `S` be a scheme. Let `B` be an algebraic space over `S`. Let
`X`, `Y` be algebraic spaces over `B`. The following are equivalent: `X` and `Y`
are Tor independent over `B`; for every commutative diagram with étale vertical
arrows `U ⟶ X`, `W ⟶ B`, `V ⟶ Y`, the spaces `U` and `V` are Tor independent over
`W`; for some such diagram with `W ⟶ B`, `U ⟶ X ×_B W`, and `V ⟶ Y ×_B W` étale
surjective, the spaces `U` and `V` are Tor independent over `W`; and for some such
covering diagram with `U`, `V`, `W` schemes, the schemes `U` and `V` are Tor
independent over `W` in the sense of `Scheme.TorIndependentOver`. -/
@[stacks 08IQ]
theorem tfae (X Y : Over B) :
    List.TFAE [AlgebraicSpace.TorIndependentOver X Y, forallEtale X Y,
      existsEtaleCover X Y, existsSchemeCover X Y] :=
  sorry

/-- Tor independence over `B` is equivalent to Tor independence of `U` and `V` over
`W` for every étale vertical diagram. -/
theorem iff_forallEtale (X Y : Over B) :
    AlgebraicSpace.TorIndependentOver X Y ↔ forallEtale X Y :=
  sorry

/-- Tor independence over `B` is equivalent to the existence of an étale-surjective
covering diagram on which `U` and `V` are Tor independent over `W`. -/
theorem iff_existsEtaleCover (X Y : Over B) :
    AlgebraicSpace.TorIndependentOver X Y ↔ existsEtaleCover X Y :=
  sorry

/-- Tor independence over `B` is equivalent to the existence of a representable
étale-surjective covering diagram on which `U` and `V` are Tor independent as
schemes over `W`. -/
theorem iff_existsSchemeCover (X Y : Over B) :
    AlgebraicSpace.TorIndependentOver X Y ↔ existsSchemeCover X Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentOver
