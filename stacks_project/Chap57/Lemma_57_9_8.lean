module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coherent.Generation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.ObjectProperty

universe u

/- Lemma 57.9.8 -/
@[stacks 0FZ7] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.exists_finiteLocallyFree_additiveExtensionStage :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [Smooth f],
      ∃ (m n : ℕ+) (G : X.Modules), SheafOfModules.IsFiniteLocallyFree G ∧
        ∀ (F : X.Modules), SheafOfModules.IsCoherent (R := X.ringCatSheaf) F →
          additiveExtensionStage
            (objectShiftInterval
              ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj G)
              (-(m : ℤ)) (m : ℤ))
            n
            ((DerivedCategory.singleFunctor X.Modules (0 : ℤ)).obj F))
