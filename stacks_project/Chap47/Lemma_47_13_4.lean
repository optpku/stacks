module

import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.FiniteCohomology
import StacksCheckRecall

universe u

/- Lemma 47.13.4: for a finite map of Noetherian rings, derived coextension of
scalars sends bounded-below derived modules with finite cohomology in every degree
to bounded-below derived modules with finite cohomology in every degree. -/
@[stacks 0A72] #check
  (CategoryTheory.ModuleCat.DerivedCoextension.mapsBoundedBelowFiniteCohomology :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      (f : A →+* B) (hf : f.Finite)
      (K : DerivedCategory (ModuleCat.{u, u} A))
      (hK_boundedBelow : ∃ n : ℤ, K.IsGE n)
      (hK_finite : ∀ i : ℤ,
        Module.Finite A
          ((DerivedCategory.homologyFunctor
            (ModuleCat.{u, u} A) i).obj K)),
      (∃ n : ℤ,
        ((CategoryTheory.ModuleCat.derivedCoextensionOfScalars f).obj K).IsGE n) ∧
        ∀ i : ℤ, Module.Finite B
          ((DerivedCategory.homologyFunctor
            (ModuleCat.{u, u} B) i).obj
        ((CategoryTheory.ModuleCat.derivedCoextensionOfScalars f).obj K)))
