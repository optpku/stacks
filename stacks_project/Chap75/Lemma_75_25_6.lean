module

public import stacks_project.Chap75.Lemma_75_25_6_Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 75.25.6: for a proper, flat, finitely presented morphism `f : X ⟶ Spec R`
and a sequential inverse system of `R`-modules with epimorphic transitions, the canonical
map from the associated module of `limit M` to `DQ_X` of the limit of the associated modules
is an isomorphism. -/
@[stacks 0D3F] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Associated.limitComparison_isIso :
    ∀ {R : Type u} [CommRing R]
      {X : AlgebraicSpace (Spec (CommRingCat.of R))}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
      [Proper f] [Flat f] [FinitePresentation f]
      (M : SequentialInverseSystem (ModuleCat.{u} R))
      [∀ n : ℕ, Epi (SequentialInverseSystem.transitionMap M (Nat.le_succ n))],
      IsIso (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Associated.limitComparison f M))
