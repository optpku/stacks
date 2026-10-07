module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion

/-!
# Valuative criterion for universal closedness

A quasi-separated universally closed morphism of algebraic spaces satisfies the
existence part of the valuative criterion. Under quasi-compactness and
quasi-separatedness, universal closedness is equivalent to existence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.Existence

/-- Lemma 67.42.2 (1): If `f : X ⟶ Y` is a quasi-separated and universally closed
morphism of algebraic spaces over a scheme `S`, then `f` satisfies the existence
part of the valuative criterion. -/
@[stacks 0A3X]
theorem of_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiSeparated f] [UniversallyClosed f] : Existence f :=
  sorry

end ValuativeCriterion.Existence

namespace UniversallyClosed

/-- Lemma 67.42.2 (2): If `f : X ⟶ Y` is a quasi-compact and quasi-separated
morphism of algebraic spaces over a scheme `S`, then `f` is universally closed
if and only if `f` satisfies the existence part of the valuative criterion. -/
@[stacks 0A3X]
theorem iff_existence {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    UniversallyClosed f ↔ ValuativeCriterion.Existence f :=
  sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicSpace
