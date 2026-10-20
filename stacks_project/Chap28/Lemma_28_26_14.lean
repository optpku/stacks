/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology

universe u

/- Lemma 28.26.14: let `X` be a scheme, `L` an ample invertible `O_X`-module, and
`i : X' ⟶ X` a morphism. Assume one of the following: (1) `i` is a quasi-compact immersion;
(2) `X'` is quasi-compact and `i` is an immersion; (3) `i` is quasi-compact and induces a
homeomorphism from `X'` onto its image; or (4) `X'` is quasi-compact and `i` induces such a
homeomorphism. These four alternatives are equivalent to `IsEmbedding i` together with
`QuasiCompact i ∨ CompactSpace X'`. Then the pullback of `L` along `i` is ample. -/
@[stacks 0B3E] #check (AlgebraicGeometry.Scheme.Modules.IsAmple.pullback_of_isEmbedding :
    ∀ {X X' : Scheme.{u}} {L : X.Modules} [AlgebraicGeometry.Scheme.Modules.Invertible L],
      AlgebraicGeometry.Scheme.Modules.IsAmple L → ∀ (i : X' ⟶ X), IsEmbedding i →
        (QuasiCompact i ∨ CompactSpace X') →
          AlgebraicGeometry.Scheme.Modules.IsAmple ((Scheme.Modules.pullback i).obj L))
