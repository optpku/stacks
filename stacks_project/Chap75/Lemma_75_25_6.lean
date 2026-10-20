module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Associated.Limit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 75.25.6: for a proper, flat morphism of finite presentation to `Spec R` and a
sequential inverse system of `R`-modules with epimorphic transitions, the canonical map
from the associated module of the inverse limit to the inverse limit of the associated
modules induces an isomorphism after applying `DQ_X` to the target. Equivalently, as in
the source proof, postcomposition is bijective on morphisms from every object of
`DerivedQCoh X`. -/
@[stacks 0D3F] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Associated.limitComparison_hom_bijective :
    ∀ {R : Type u} [CommRing R]
      {X : AlgebraicSpace (Spec (CommRingCat.of R))}
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
      [Proper f] [Flat f] [FinitePresentation f]
      (M : SequentialInverseSystem (ModuleCat.{u} R))
      [∀ n : ℕ, Epi (SequentialInverseSystem.transitionMap M (Nat.le_succ n))]
      (E : DerivedQCoh X),
      Function.Bijective
        (fun g : E.obj ⟶
            (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Associated.single f (limit M)).obj =>
          g ≫ AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.Associated.limitComparison f M))
