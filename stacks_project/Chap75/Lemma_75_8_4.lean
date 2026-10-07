module

public import stacks_project.Chap75.Lemma_75_8_4_Linear
public import stacks_project.Chap75.Lemma_75_8_4_Ext
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure

universe u

/- Lemma 75.8.4: if `A` is Noetherian and `X` is a proper algebraic space over `A`,
then every `A`-module `Ext⁽n⁾(K, L)` is finite when `K` has bounded-above coherent
cohomology and `L` has bounded-below coherent cohomology. -/
@[stacks 0D0T] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.DerivedExt.finite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
      (K L : ModuleDerived X)
      (hK_coherent : DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf X)) K)
      (hK_boundedAbove :
        (t.minus : ObjectProperty (ModuleDerived X)) K)
      (hL_coherent : DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf X)) L)
      (hL_boundedBelow :
        (t.plus : ObjectProperty (ModuleDerived X)) L)
      (n : ℤ),
      Module.Finite A
        (AlgebraicGeometry.AlgebraicSpace.Hom.DerivedExt.value f K L n))
