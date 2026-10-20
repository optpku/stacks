/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence.EtaleLocal
import StacksCheckRecall

/-!
# Étale-local characterizations of Tor independence

Lemma 75.20.3 records that Tor independence of algebraic spaces over a common base
is equivalent to the corresponding condition on every étale vertical diagram, on
some étale-surjective covering diagram, and on some representable scheme covering
diagram using scheme-level Tor independence.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 75.20.3: let `S` be a scheme. Let `B` be an algebraic space over `S`. Let
`X`, `Y` be algebraic spaces over `B`. The following are equivalent: `X` and `Y`
are Tor independent over `B`; for every commutative diagram with étale vertical
arrows `U ⟶ X`, `W ⟶ B`, `V ⟶ Y`, the spaces `U` and `V` are Tor independent over
`W`; for some such diagram with `W ⟶ B`, `U ⟶ X ×_B W`, and `V ⟶ Y ×_B W` étale
surjective, the spaces `U` and `V` are Tor independent over `W`; and for some such
covering diagram with `U`, `V`, `W` schemes, the schemes `U` and `V` are Tor
independent over `W` in the sense of `Scheme.TorIndependentOver`. -/
@[stacks 08IQ] #check (AlgebraicGeometry.AlgebraicSpace.TorIndependentOver.tfae :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (X Y : Over B),
    List.TFAE [AlgebraicSpace.TorIndependentOver X Y,
      AlgebraicSpace.TorIndependentOver.forallEtale X Y,
      AlgebraicSpace.TorIndependentOver.existsEtaleCover X Y,
      AlgebraicSpace.TorIndependentOver.existsSchemeCover X Y])
