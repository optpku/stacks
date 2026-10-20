module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Setoids
import StacksCheckRecall

/-!
# Algebraic stacks with no automorphisms

An algebraic stack over a scheme `S` is representable by an algebraic space if
and only if it is Deligne-Mumford and a stack in setoids, equivalently if it is
Deligne-Mumford and the canonical inertia 1-morphism is an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia (forget)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 94.13.2 (1): let `S` be a scheme contained in `Sch_fppf`. Let `X` be
an algebraic stack over `S`. Then `X` is a Deligne-Mumford stack and a stack
in setoids if and only if `X` is a Deligne-Mumford stack and the canonical
1-morphism `Inertia.forget X : inertia X ⟶ X` is an equivalence. -/
@[stacks 045H]
#check (AlgebraicGeometry.AlgebraicStack.inSetoids_iff_inertia_forget :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (DeligneMumfordStack X ∧
        IsStack.InSetoids (Scheme.fppfTopology.over S) X.p) ↔
      (DeligneMumfordStack X ∧
        (toBasedFunctor (forget.{u + 1, u, u, u + 1} X)).IsEquivalence))

/- Lemma 94.13.2 (2): let `S` be a scheme contained in `Sch_fppf`. Let `X` be
an algebraic stack over `S`. Then `X` is a Deligne-Mumford stack and a stack
in setoids if and only if `X` is representable by an algebraic space. -/
@[stacks 045H]
#check (AlgebraicGeometry.AlgebraicStack.isRepresentableByAlgebraicSpace_iff_deligneMumford_inSetoids :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (DeligneMumfordStack X ∧
        IsStack.InSetoids (Scheme.fppfTopology.over S) X.p) ↔
      IsRepresentableByAlgebraicSpace X)

/- Lemma 94.13.2 (3): let `S` be a scheme contained in `Sch_fppf`. Let `X` be
an algebraic stack over `S`. Then `X` is a Deligne-Mumford stack such that the
canonical 1-morphism `Inertia.forget X : inertia X ⟶ X` is an equivalence if
and only if `X` is representable by an algebraic space. -/
@[stacks 045H]
#check (AlgebraicGeometry.AlgebraicStack.isRepresentableByAlgebraicSpace_iff_deligneMumford_inertia :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    (DeligneMumfordStack X ∧
        (toBasedFunctor (forget.{u + 1, u, u, u + 1} X)).IsEquivalence) ↔
      IsRepresentableByAlgebraicSpace X)

end AlgebraicGeometry.AlgebraicStack
