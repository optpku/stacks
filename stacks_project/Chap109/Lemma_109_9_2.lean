module

public import stacks_project.Chap67.Lemma_67_22_5_EtaleLocal
public import stacks_project.Chap76.Lemma_76_26_1_FiberStalkCohenMacaulay
public import stacks_project.Chap109.Lemma_109_9_1_Substack

/-!
# The h0,1 locus of curves is contained in the CM,1 locus

As open substacks of 𝒞urves, 𝒞urves^{h0, 1} is contained in 𝒞urves^{CM, 1}.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace
open Scheme.Germ.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.9.2: we have 𝒞urves^{h0, 1} ⊂ 𝒞urves^{CM, 1} as open substacks of 𝒞urves. -/
@[stacks 0E6J]
theorem h0Dim1_le_cohenMacaulayDim1 (S : Scheme.{u}) :
    h0Dim1 S ≤ fun P ↦
      (∀ x : Points (space P),
          FlatAt (hom P) x ∧
            existsEtaleSquareAt fiberStalkCohenMacaulay (hom P) x) ∧
        RelativeDimension (hom P) 1 :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
