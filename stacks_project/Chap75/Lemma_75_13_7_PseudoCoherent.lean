module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Noetherian

/-!
# Pseudo-coherent complexes on Noetherian algebraic spaces

On a Noetherian algebraic space, pseudo-coherence of an object of `D_QCoh(𝒪_X)` is
characterized by bounded-above coherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.isMPseudoCoherent_iff_boundedAbove_and_cohomology_coherent_ge :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X] (E : DerivedQCoh X) (m : ℤ),
      IsMPseudoCoherent X E.obj m ↔
        (t.minus : ObjectProperty (ModuleDerived X)) E.obj ∧
          ∀ i : ℤ, m ≤ i →
            ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj).IsCoherent)

#check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.isPseudoCoherent_iff_boundedAbove_and_cohomology_coherent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X] (E : DerivedQCoh X),
      IsPseudoCoherent X E.obj ↔
        (t.minus : ObjectProperty (ModuleDerived X)) E.obj ∧
          DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent (structureSheaf X)) E.obj)
