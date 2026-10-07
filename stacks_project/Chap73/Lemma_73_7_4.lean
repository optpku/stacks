module

public import stacks_project.Chap73.Definition_73_7_1_FppfCover

/-!
# Scheme refinements of fppf coverings of algebraic spaces

An fppf covering family of an algebraic space admits an fppf refinement whose
sources are schemes over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 73.7.4: let `S` be a scheme and let `X` be an algebraic space over
`S`. If `{f i : X_i i ⟶ X}` is an fppf covering of `X`, then there exists a
refinement `{h i ≫ f i : ofOver (T i) ⟶ X}` which is an fppf covering and such
that each `T i` is a scheme over `S`. Each `ofOver (T i)` is a scheme by
`instIsScheme_ofOver`. -/
@[stacks 042T]
theorem FppfCovering.exists_schemeRefinement {S : Scheme.{u}}
    {X : AlgebraicSpace S} {ι : Type v} (X_i : ι → AlgebraicSpace S)
    (f : ∀ i, X_i i ⟶ X) (hf : FppfCovering X_i f) :
    ∃ (T : ι → Over S) (h : ∀ i, ofOver (T i) ⟶ X_i i),
      FppfCovering (fun i ↦ ofOver (T i)) (fun i ↦ h i ≫ f i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
