module

public import stacks_project.Chap100.Lemma_100_9_7_Presentation
public import stacks_project.Chap100.Lemma_100_9_7_Subspace
import StacksCheckRecall

/-!
# Immersions into presentations

An immersion into the quotient stack of a smooth groupoid in algebraic spaces
cuts out an invariant locally closed subspace of the object space, whose
restricted groupoid presents the source of the immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 100.9.7 (1): let `G` be a smooth groupoid in algebraic spaces and let
`i : Z ⟶ [U / R]` be an immersion of algebraic stacks. Then the recovered subspace
`subspace G i ⊂ U` is `R`-invariant, the restriction `R_Z` is `restrict G (subspace G i)`,
and `presentationHom G i : [Z / R_Z] ⟶ Z` is a presentation. -/
@[stacks 0505]
theorem exists_invariantLocallyClosedSubspace {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [Immersion i] :
    G.IsLocallyClosedInvariant (subspace G i) ∧
      (toBasedFunctor (presentationHom G i)).IsEquivalence :=
  sorry

/- Lemma 100.9.7 (2): the two paths `restrictQuotientHom G (subspace G i)` and
`presentationHom G i ≫ i` of the triangle are 2-isomorphic. -/
@[stacks 0505] #check
  (triangleIso :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
      (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
      (i : Z ⟶ G.quotientStack) [Immersion i],
      restrictQuotientHom G (subspace G i) ≅ presentationHom G i ≫ i)

/-- Lemma 100.9.7 (3): if in addition `i` is a closed immersion, then the recovered subspace
is a closed subspace of `U`. -/
@[stacks 0505]
theorem subspace_isClosed {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [ClosedImmersion i] :
    (closedSubspace G i).toLocallyClosed = subspace G i ∧
      AlgebraicSpace.IsClosedImmersion (subspace G i).ι :=
  sorry

/-- Lemma 100.9.7 (4): if in addition `i` is an open immersion, then the recovered subspace
is an open subspace of `U`. -/
@[stacks 0505]
theorem subspace_isOpen {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] {Z : GroupoidsOver S} [AlgebraicStack Z]
    (i : Z ⟶ G.quotientStack) [OpenImmersion i] :
    (openSubspace G i).toLocallyClosed = subspace G i ∧
      AlgebraicSpace.IsOpenImmersion (subspace G i).ι :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
