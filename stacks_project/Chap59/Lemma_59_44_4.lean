/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyC
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

/- Lemma 59.44.4: an integral morphism of schemes whose underlying map is a
homeomorphism onto a closed subset satisfies Property (C). -/
@[stacks 04DW] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.hasPropertyC_of_isIntegralHom_isClosedEmbedding :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f],
      Topology.IsClosedEmbedding f.base →
        AlgebraicGeometry.Scheme.Etale.SmallToBig.hasPropertyC f)
