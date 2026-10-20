module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Affineness of immersions

An immersion is affine when there is an open subscheme whose inclusion and the restricted
morphism are affine, and the part of the immersion's range over the complement is closed.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An immersion is affine if there is an open subscheme whose inclusion and the restricted
morphism are affine, and the part of its range over the complement is closed. -/
theorem isAffineHom_of_exists_affine_restrict_and_closed_compl
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j]
    (h : ∃ U : X.Opens,
      IsAffineHom U.ι ∧ IsAffineHom (j ∣_ U) ∧
        IsClosed (Set.range j ∩ (U : Set X)ᶜ)) :
    IsAffineHom j := sorry

/-- If an immersion admits an open subscheme whose inclusion and restricted morphism are affine,
and the part of its range over the complement is closed, then an affine target makes its source
affine. -/
theorem isAffine_of_exists_affine_restrict_and_closed_compl
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsImmersion j] [IsAffine X]
    (h : ∃ U : X.Opens,
      IsAffineHom U.ι ∧ IsAffineHom (j ∣_ U) ∧
        IsClosed (Set.range j ∩ (U : Set X)ᶜ)) :
    IsAffine Y := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- If the inverse image of a basic open under an immersion into an affine scheme is affine,
and the part of the immersion's range in the complementary zero locus is closed, then the
source is affine. -/
theorem isAffine_of_basicOpen_preimage_of_isClosed
    {A : CommRingCat.{u}} {V : Scheme.{u}} (j : V ⟶ Spec A)
    [IsImmersion j] (f : A)
    (h_affine : IsAffineOpen (j ⁻¹ᵁ PrimeSpectrum.basicOpen f))
    (h_closed : IsClosed (Set.range j ∩ PrimeSpectrum.zeroLocus ({f} : Set A))) :
    IsAffine V := by
  let U : (Spec A).Opens := (Spec A).basicOpen ((Scheme.ΓSpecIso A).inv f)
  have h_U : U = PrimeSpectrum.basicOpen f := by
    simpa [U] using AlgebraicGeometry.basicOpen_eq_of_affine f
  have h_Uι : IsAffineHom U.ι := by
    dsimp [U]
    infer_instance
  have h_target : IsAffine U := by
    dsimp [U]
    exact (isAffineOpen_top (Spec A)).basicOpen ((Scheme.ΓSpecIso A).inv f)
  have h_source : IsAffine (j ⁻¹ᵁ U) := by
    rw [h_U]
    simpa [IsAffineOpen] using h_affine
  have h_restrict : IsAffineHom (j ∣_ U) :=
    @AlgebraicGeometry.isAffineHom_of_isAffine (j ⁻¹ᵁ U) U (j ∣_ U) h_source h_target
  have h_U_set := congrArg (fun W : (Spec A).Opens ↦ (W : Set (Spec A))) h_U
  have h_closed' : IsClosed (Set.range j ∩ (U : Set (Spec A))ᶜ) := by
    rw [h_U_set]
    change IsClosed (Set.range j ∩ ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A))ᶜ))
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    convert h_closed using 1
    ext x
    constructor
    · rintro ⟨hx_range, hx_zero⟩
      refine ⟨hx_range, ?_⟩
      by_contra hx_mem
      exact hx_zero hx_mem
    · rintro ⟨hx_range, hx_zero⟩
      refine ⟨hx_range, ?_⟩
      intro hx_not_mem
      exact hx_not_mem hx_zero
  refine AlgebraicGeometry.isAffine_of_exists_affine_restrict_and_closed_compl j ?_
  exact ⟨U, h_Uι, h_restrict, h_closed'⟩

end AlgebraicGeometry.Scheme
