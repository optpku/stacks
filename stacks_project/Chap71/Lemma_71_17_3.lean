module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.BaseChange
import StacksCheckRecall

/-!
# Lemma 71.17.3

The blowup of the inverse image of a closed subspace along a flat morphism of
algebraic spaces fits in a cartesian square with the blowup of the original
closed subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u

/- Lemma 71.17.3: let `S` be a scheme, let `f : X₁ ⟶ X₂` be a flat morphism of
algebraic spaces over `S`, and let `Z₂ ⊂ X₂` be a closed subspace. Write `Z₁`
for the inverse image `Z₂.inverseImageSubspace f`, and let `bᵢ : Xᵢ' ⟶ Xᵢ`
be blowups of `Zᵢ` in `Xᵢ`. Then there exists a morphism `g' : X₁' ⟶ X₂'`
making `CategoryTheory.IsPullback g' b₁ b₂ f` a cartesian square over `S`. -/
@[stacks 085S] #check
  (AlgebraicGeometry.AlgebraicSpace.IsBlowup.exists_isPullback_of_flat :
    ∀ {S : Scheme.{u}} {X₁ X₂ X₁' X₂' : AlgebraicSpace S}
      (f : X₁ ⟶ X₂) [Flat f] (Z₂ : ClosedSubspace X₂)
      (b₁ : X₁' ⟶ X₁) (b₂ : X₂' ⟶ X₂)
      [IsBlowup b₁ (Z₂.inverseImageSubspace f)] [IsBlowup b₂ Z₂],
      ∃ g' : X₁' ⟶ X₂', CategoryTheory.IsPullback g' b₁ b₂ f)
