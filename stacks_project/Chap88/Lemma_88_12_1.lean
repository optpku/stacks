module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Situation_87_21_2_MorphismProperty
public import stacks_project.Chap88.Lemma_88_12_1_FiniteTypeReduction

/-!
# Finite type on reductions is a local morphism property
-/

@[expose] public section

universe u

open TopologicalRing RingHom

namespace TopologicalRing

/-- Lemma 88.12.1: For an arrow `φ : A →+* B` in `WAdm^count`, the property
that the induced ring homomorphism
`A ⧸ topologicalNilradical A →+* B ⧸ topologicalNilradical B` is of finite
type is a local property as defined in Situation 87.21.2. -/
@[stacks 0GC2]
theorem isLocalMorphismProperty_isFiniteTypeOnReduction :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsFiniteTypeOnReduction :=
  sorry

end TopologicalRing
