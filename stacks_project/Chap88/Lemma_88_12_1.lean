/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.FiniteType.Reduction
import StacksCheckRecall

/-!
# Finite type on reductions is a local morphism property
-/

@[expose] public section

universe u

open TopologicalRing RingHom

/- Lemma 88.12.1: For an arrow `φ : A →+* B` in `WAdm^count`, the property
that the induced ring homomorphism
`A ⧸ topologicalNilradical A →+* B ⧸ topologicalNilradical B` is of finite
type is a local property as defined in Situation 87.21.2. -/
@[stacks 0GC2] #check (TopologicalRing.isLocalMorphismProperty_isFiniteTypeOnReduction :
    TopologicalRing.IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsFiniteTypeOnReduction)
