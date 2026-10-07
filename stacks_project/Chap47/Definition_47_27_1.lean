module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Relative
import StacksCheckRecall

universe u

/- Definition 47.27.1: for a flat finitely presented commutative algebra `A` over `R`,
a relative dualizing complex is an `R`-perfect object `K` of `D(A)` whose derived Hom over
`A ⊗[R] A` from the diagonal copy of `A` to the base change of `K` is isomorphic to `A`. -/
@[stacks 0E2C] #check (CategoryTheory.DerivedCategory.IsRelativeDualizingComplex :
  ∀ (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A],
    _root_.DerivedCategory (ModuleCat A) → Prop)
