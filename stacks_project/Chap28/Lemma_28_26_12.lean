module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Ample
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.26.12: if a quasi-compact scheme `X` admits an open immersion
`j : X ⟶ Proj 𝒜`, then some positive canonical twist pulls back to an ample invertible module on
`X`. -/
@[stacks 01Q2] #check
  (AlgebraicGeometry.exists_pos_isAmpleObject_pullback_twistingSheaf_of_isOpenImmersion :
    ∀ {A : Type u} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      {X : Scheme.{u}} (j : X ⟶ Proj 𝒜) [IsOpenImmersion j],
      IsCompact (Set.univ : Set X) →
        ∃ d : ℕ, 0 < d ∧
          Scheme.Modules.isAmpleObject
            ((Scheme.Modules.pullback j).obj
              (Proj.AssociatedModule.twistingSheaf 𝒜 (d : ℤ))))
