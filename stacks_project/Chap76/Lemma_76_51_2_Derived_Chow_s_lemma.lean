module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Chow.Derived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Chow.Derived.Restriction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.51.2 (Derived Chow's lemma). Let `A` be a ring and let `X` be a
separated algebraic space of finite presentation over `A`. For every point
`x` of `Points X` there exist `n : ℕ`, a closed subspace `Z` of
`ProjectiveSpace n X`, a point `z` of `Points Z.X`, an open `V` of
`ofScheme n (Spec (CommRingCat.of A))`, and `E` in
`ModuleDerived (ProjectiveSpace n X)` such that `Z.ι` is of finite presentation,
`c : Z ⟶ ℙⁿ_A` is a closed immersion over `V`, the restriction of `b : Z ⟶ X` to
`W = c⁻¹(V)` is étale, `z` lies in `W` with `b(z) = x`,
`E` restricted to `X ×_A V` is isomorphic to `(b, c)_* 𝒪_Z` restricted to
`X ×_A V`, and `E` is pseudo-coherent and supported on `Z`. -/
@[stacks 0CTR] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedChowPresentation.exists_of_separated_finitePresentation :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [Separated (SchemeRealization.toBase X)] [FinitePresentation (SchemeRealization.toBase X)]
      (x : Points X), Nonempty (DerivedChowPresentation x))
