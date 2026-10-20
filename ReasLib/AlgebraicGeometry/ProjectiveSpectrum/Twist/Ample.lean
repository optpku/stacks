module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.CompactOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample

/-!
# Ample twists on projective spectra

A quasi-compact open subscheme of a projective spectrum admits a positive canonical twist whose
pullback is an ample invertible module.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- For a quasi-compact scheme openly immersed in a projective spectrum, some positive canonical
twist pulls back to an ample invertible module. -/
theorem exists_pos_isAmpleObject_pullback_twistingSheaf_of_isOpenImmersion
    {A : Type u} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
    {X : Scheme.{u}} (j : X ⟶ Proj 𝒜) [IsOpenImmersion j]
    (hX : IsCompact (Set.univ : Set X)) :
    ∃ d : ℕ, 0 < d ∧
      Scheme.Modules.isAmpleObject
        ((Scheme.Modules.pullback j).obj
          (Proj.AssociatedModule.twistingSheaf 𝒜 (d : ℤ))) := sorry

end AlgebraicGeometry
