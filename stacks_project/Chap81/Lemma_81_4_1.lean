module

public import stacks_project.Chap81.Lemma_81_4_1_Descent

/-!
# Lemma 81.4.1

The functor from sheaves on the small étale site of an algebraic space to
descent data for étale sheaves along an étale covering is an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 81.4.1: Let `S` be a scheme. Let `{f i : Xᵢ i ⟶ X}` be an étale covering
of algebraic spaces. The functor `Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤
etaleCoveringDescent f` is an equivalence of categories. -/
@[stacks 0GFS]
theorem sheafToEtaleCoveringDescent_isEquivalence
    {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type u}
    {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X) [∀ i, Etale (f i)]
    (h_cover : (⋃ i, Set.range (Points.map (f i))) = Set.univ) :
    (sheafToEtaleCoveringDescent f).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
