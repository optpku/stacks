/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap71.Definition_71_17_1_Blowup

/-!
# Lemma 71.17.3

The blowup of the inverse image of a closed subspace along a flat morphism of
algebraic spaces fits in a cartesian square with the blowup of the original
closed subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- Lemma 71.17.3: let `S` be a scheme, let `f : X₁ ⟶ X₂` be a flat morphism of
algebraic spaces over `S`, and let `Z₂ ⊂ X₂` be a closed subspace. Write `Z₁`
for the inverse image `Z₂.inverseImage f`, and let `πᵢ` be chosen blowups of
`Zᵢ` in `Xᵢ`. Then there exists a morphism `g' : π₁.space ⟶ π₂.space` making
`IsPullback g' π₁.hom π₂.hom f` a cartesian square of algebraic spaces over
`S`. -/
@[stacks 085S]
theorem exists_isPullback_of_flat {S : Scheme.{u}} {X₁ X₂ : AlgebraicSpace S}
    (f : X₁ ⟶ X₂) [Flat f] (Z₂ : ClosedSubspace X₂)
    (π₁ : along (Z₂.inverseImage f)) (π₂ : along Z₂) :
    ∃ g' : π₁.space ⟶ π₂.space, IsPullback g' π₁.hom π₂.hom f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
