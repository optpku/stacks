module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.RingTheory.Etale.WContractible

/-!
# Affine w-contractible covers in the pro-étale topology

Every scheme admits a pro-étale cover by affine spectra of w-contractible rings.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Proetale

/-- Every scheme admits a pro-étale cover whose members are affine with
w-contractible rings of global sections. -/
theorem exists_affine_wContractibleRing_cover (T : Scheme.{u}) :
    ∃ 𝒰 : T.Cover.{u} Scheme.proetalePrecoverage,
      ∀ i, IsAffine (𝒰.X i) ∧ IsWContractibleRing.{u, u} Γ(𝒰.X i, ⊤) := sorry

/-- Every scheme admits a jointly surjective weakly étale family of maps from
spectra of w-contractible rings which covers in the pro-étale precoverage. -/
theorem exists_affineCover_isWContractibleRing (T : Scheme.{u}) :
    ∃ 𝒰 : T.AffineCover.{u} (@WeaklyEtale),
      Presieve.ofArrows (fun j ↦ Spec (𝒰.X j)) 𝒰.f ∈ Scheme.proetalePrecoverage T ∧
        ∀ j, IsWContractibleRing.{u, u} (𝒰.X j) := sorry

end AlgebraicGeometry.Scheme.Proetale
