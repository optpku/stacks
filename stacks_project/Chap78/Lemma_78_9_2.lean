module

public import stacks_project.Chap78.Lemma_78_9_2_PseudoTorsor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ModObj

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
  (X : GroupAlgebraicSpace.Action G)

/- Lemma 78.9.2 (1): The algebraic space `X` is a pseudo `G`-torsor if and only if
for every scheme `T` over `B` the set `X(T)` is empty or the action of `G(T)` on
`X(T)` is simply transitive. -/
@[stacks 04TX] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.isPseudoTorsor_iff_schemePoints G X :
    CategoryTheory.Mod.IsPseudoTorsor X ↔
      ∀ (T : Over S) (t : AlgebraicSpace.ofOver T ⟶ B)
        (x y : Over.mk t ⟶ X.X), ∃! g : Over.mk t ⟶ G.X, g • x = y)

variable [CategoryTheory.Mod.IsPseudoTorsor X]

/- Lemma 78.9.2 (2): A pseudo `G`-torsor `X` is trivial if and only if the morphism
`X ⟶ B` has a section. -/
@[stacks 04TX] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.isTrivial_iff_exists_section G X :
    CategoryTheory.Mod.IsTrivial X ↔
      ∃ s : B ⟶ X.X.left, s ≫ X.X.hom = 𝟙 B)
