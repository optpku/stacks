module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

@[expose] public section

namespace AlgebraicGeometry

noncomputable section

open CategoryTheory Scheme

universe u

variable {X : Scheme.{u}}

/-- The ideal sheaf defining the scheme-theoretic closure of an open subscheme
`U ⊆ X`. -/
def schemeTheoreticClosureIdeal (U : X.Opens) : X.IdealSheafData :=
  U.ι.ker

/-- The defining ideal of the scheme-theoretic closure is the kernel of the
open immersion. -/
@[simp]
theorem schemeTheoreticClosureIdeal_eq_ker (U : X.Opens) :
    schemeTheoreticClosureIdeal U = U.ι.ker := sorry

/-- The scheme associated to the ideal sheaf defining the scheme-theoretic
closure of an open subscheme `U ⊆ X`. -/
def schemeTheoreticClosure (U : X.Opens) : Scheme :=
  (schemeTheoreticClosureIdeal U).subscheme

/-- The canonical closed immersion of the scheme-theoretic closure into `X`. -/
def schemeTheoreticClosureι (U : X.Opens) : schemeTheoreticClosure U ⟶ X :=
  (schemeTheoreticClosureIdeal U).subschemeι

/-- The scheme-theoretic closure is the image of the open inclusion. -/
@[simp]
theorem schemeTheoreticClosure_eq_image (U : X.Opens) :
    schemeTheoreticClosure U = Scheme.Hom.image U.ι := sorry

/-- The closure immersion is the canonical image immersion. -/
@[simp]
theorem schemeTheoreticClosureι_eq_imageι (U : X.Opens) :
    schemeTheoreticClosureι U = Scheme.Hom.imageι U.ι := sorry

/-- The ideal sheaf defining the scheme-theoretic closure of `U ∩ V` inside
an open subscheme `V ⊆ X`. -/
def schemeTheoreticClosureInIdeal (U V : X.Opens) : V.toScheme.IdealSheafData :=
  (X.homOfLE (inf_le_right : U ⊓ V ≤ V)).ker

/-- The ideal defining the relative scheme-theoretic closure is the kernel of
the inclusion `U ⊓ V ⟶ V`. -/
@[simp]
theorem schemeTheoreticClosureInIdeal_eq_ker (U V : X.Opens) :
    schemeTheoreticClosureInIdeal U V =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V)).ker := sorry

/-- The scheme associated to the ideal sheaf defining the scheme-theoretic
closure of `U ∩ V` inside an open subscheme `V ⊆ X`. -/
def schemeTheoreticClosureIn (U V : X.Opens) : Scheme :=
  (schemeTheoreticClosureInIdeal U V).subscheme

/-- The canonical closed immersion of the relative scheme-theoretic closure
into `V`. -/
def schemeTheoreticClosureInι (U V : X.Opens) : schemeTheoreticClosureIn U V ⟶ V :=
  (schemeTheoreticClosureInIdeal U V).subschemeι

/-- The relative closure is the image of the inclusion `U ⊓ V ⟶ V`. -/
@[simp]
theorem schemeTheoreticClosureIn_eq_image (U V : X.Opens) :
    schemeTheoreticClosureIn U V =
      Scheme.Hom.image (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) := sorry

/-- The relative closure immersion is the canonical image immersion. -/
@[simp]
theorem schemeTheoreticClosureInι_eq_imageι (U V : X.Opens) :
    schemeTheoreticClosureInι U V =
      Scheme.Hom.imageι (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) := sorry

/-- An open subscheme is scheme-theoretically dense when every relative
scheme-theoretic closure has bottom defining ideal. -/
def schemeTheoreticallyDense (U : X.Opens) : Prop :=
  ∀ V : X.Opens, schemeTheoreticClosureInIdeal U V = ⊥

/-- Scheme-theoretic density means that every relative closure has bottom
defining ideal. -/
@[simp]
theorem schemeTheoreticallyDense_iff (U : X.Opens) :
    schemeTheoreticallyDense U ↔
      ∀ V : X.Opens, schemeTheoreticClosureInIdeal U V = ⊥ := sorry

/-- Scheme-theoretic density is equivalent to scheme-theoretic dominance of
every inclusion `U ⊓ V ⟶ V`. -/
theorem schemeTheoreticallyDense_iff_forall_isSchemeTheoreticallyDominant
    (U : X.Opens) :
    schemeTheoreticallyDense U ↔
      ∀ V : X.Opens,
        IsSchemeTheoreticallyDominant
          (X.homOfLE (inf_le_right : U ⊓ V ≤ V)) := sorry

/-- The intersection of two scheme-theoretically dense open subschemes is
scheme-theoretically dense. -/
theorem schemeTheoreticallyDense_inf {U V : X.Opens}
    (hU : schemeTheoreticallyDense U) (hV : schemeTheoreticallyDense V) :
    schemeTheoreticallyDense (U ⊓ V) := sorry

/-- The open range of an open immersion is scheme-theoretically dense exactly
when its canonical structure-sheaf morphism is monic. -/
theorem schemeTheoreticallyDense_opensRange_iff_mono
    {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    schemeTheoreticallyDense j.opensRange ↔ Mono j.c := sorry

/-- A quasi-compact open subscheme is scheme-theoretically dense exactly when
its scheme-theoretic closure immersion is an isomorphism. -/
theorem schemeTheoreticallyDense_iff_isIso_schemeTheoreticClosureι
    (U : X.Opens) [QuasiCompact U.ι] :
    schemeTheoreticallyDense U ↔ IsIso (schemeTheoreticClosureι U) := sorry

end

end AlgebraicGeometry
