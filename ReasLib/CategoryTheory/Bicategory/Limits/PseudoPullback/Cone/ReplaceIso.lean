module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone

/-!
# Replacement of the comparison of a pseudopullback cone

The outer comparison can be replaced while retaining the apex and projections.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- Rebuild a pseudopullback cone with the same apex and projections, replacing
only the outer comparison 2-isomorphism. -/
def replaceIso (sq : PseudoPullbackCone f g) (iso' : sq.fst ≫ f ≅ sq.snd ≫ g) :
    PseudoPullbackCone f g where
  pt := sq.pt
  fst := sq.fst
  snd := sq.snd
  iso := iso'

/-- The apex of `replaceIso` is the original apex. -/
@[simp]
theorem replaceIso_pt (sq : PseudoPullbackCone f g)
    (iso' : sq.fst ≫ f ≅ sq.snd ≫ g) : (replaceIso sq iso').pt = sq.pt :=
  sorry

/-- The first projection of `replaceIso` is the original first projection. -/
@[simp]
theorem replaceIso_fst (sq : PseudoPullbackCone f g)
    (iso' : sq.fst ≫ f ≅ sq.snd ≫ g) : (replaceIso sq iso').fst = sq.fst :=
  sorry

/-- The second projection of `replaceIso` is the original second projection. -/
@[simp]
theorem replaceIso_snd (sq : PseudoPullbackCone f g)
    (iso' : sq.fst ≫ f ≅ sq.snd ≫ g) : (replaceIso sq iso').snd = sq.snd :=
  sorry

/-- The comparison 2-isomorphism of `replaceIso` is the newly supplied cell. -/
@[simp]
theorem replaceIso_iso (sq : PseudoPullbackCone f g)
    (iso' : sq.fst ≫ f ≅ sq.snd ≫ g) : (replaceIso sq iso').iso = iso' :=
  sorry

end CategoryTheory.Bicategory.PseudoPullbackCone

