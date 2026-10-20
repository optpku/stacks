module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PerfectApproximation.ElementaryDistinguishedSquare
import StacksCheckRecall

/-!
# Perfect approximation along an elementary distinguished square

On an elementary distinguished square, a perfect approximation of the restricted
triple on `V` extends to `X` when the closed support lies in `|X| \ |U|` and the
cohomology sheaves of `E` from degree `m` onward are supported on that closed set.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare
open TopologicalSpace

noncomputable section

universe u

/- Lemma 75.14.4: let `S` be a scheme and let `(U ⊂ X, f : V ⟶ X)` be an elementary
distinguished square of algebraic spaces over `S`. Let `T` be a closed subset of
`|X| \ |U|` and let `(T, E, m)` be a triple as in `HasPerfectApproximation`. If
approximation holds for `(f⁻¹T, E|_V, m)`, and the sheaves `H^i(E)` for `m ≤ i` are
supported on `T`, then approximation holds for `(T, E, m)`. The source morphism
`j : V → X` is this étale map `f`, and `j⁻¹T` is `T.preimage (Points.continuous_map f)`. -/
@[stacks 08HL] #check
  (AlgebraicGeometry.AlgebraicSpace.HasPerfectApproximation.of_isElementaryDistinguishedSquare :
    ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S} (j : U ⟶ X) (f : V ⟶ X)
      [Etale f] [IsElementaryDistinguishedSquare j f] (T : Closeds (Points X))
      (hT : (T : Set (Points X)) ⊆ (toOpenSubspace j f).pointsSetᶜ) (E : DerivedQCoh X)
      (m : ℤ)
      (hV : HasPerfectApproximation (T.preimage (Points.continuous_map f))
        (DerivedQCoh.restrict f E) m)
      (hE : ∀ i : ℤ, m ≤ i →
        Modules.moduleSupportedOn (T : Set (Points X))
          ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj)),
      HasPerfectApproximation T E m)
