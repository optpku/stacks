module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf.Refinement
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 73.7.4: Let `S` be a scheme, and let `X` be an algebraic space over
`S`. Suppose that `𝒰 = { f_i : X_i → X }` is an fppf covering of `X`. Then
there exists a refinement `𝒱 = { h_i ≫ f_i : ofOver (T_i) → X }` of `𝒰`
which is an fppf covering such that each `T_i` is a scheme. -/
@[stacks 042T] #check
  (AlgebraicGeometry.AlgebraicSpace.FppfCovering.exists_schemeRefinement :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
      (X_i : ι → AlgebraicSpace S) (f : ∀ i, X_i i ⟶ X)
      (hf : AlgebraicGeometry.AlgebraicSpace.FppfCovering X_i f),
      ∃ (T : ι → Over S) (h : ∀ i, ofOver (T i) ⟶ X_i i),
        AlgebraicGeometry.AlgebraicSpace.FppfCovering
          (fun i ↦ ofOver (T i)) (fun i ↦ h i ≫ f i))
