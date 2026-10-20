module

public import stacks_project.Chap109.Lemma_109_17_1_Points
public import stacks_project.Chap109.Lemma_109_17_1_Inclusion

/-!
# Lemma 109.17.1

The inclusion `|𝒞urves^{smooth}| ⊂ |𝒞urves^{lci+}|` is that of an open dense
subset of the canonical topology on points of the lci-plus open substack of
curves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- Lemma 109.17.1 (1): the inclusion `|𝒞urves^{smooth}| ⊂ |𝒞urves^{lci+}|` is
that of an open subset of `|𝒞urves^{lci+}|`. -/
@[stacks 0E86]
theorem isOpen_smoothPointsSet (S : Scheme.{u}) : IsOpen (smoothPointsSet S) :=
  sorry

/-- Lemma 109.17.1 (2): the inclusion `|𝒞urves^{smooth}| ⊂ |𝒞urves^{lci+}|` is
that of a dense subset of `|𝒞urves^{lci+}|`. -/
@[stacks 0E86]
theorem dense_smoothPointsSet (S : Scheme.{u}) : Dense (smoothPointsSet S) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
