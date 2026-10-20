module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic

/-!
# Extending admissible blowups

This file records extension results for admissible blowups from quasi-compact open subschemes.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- An admissible blowup of a quasi-compact open subscheme of a quasi-compact quasi-separated
scheme extends to an admissible blowup of the whole scheme whose center avoids a prescribed
quasi-compact open, with the original blowup recovered by restriction. -/
theorem exists_isAdmissibleBlowup_restrict_iso_of_isAdmissibleBlowup_inter
    {X V' : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : X.Opens) (hU : QuasiCompact U.ι) (hV : QuasiCompact V.ι)
    (b : V' ⟶ V.toScheme) (hb : IsAdmissibleBlowup (V.ι ⁻¹ᵁ U) b) :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X),
      IsAdmissibleBlowup U π ∧ Nonempty (Over.mk (π ∣_ V) ≅ Over.mk b) := sorry

end AlgebraicGeometry
