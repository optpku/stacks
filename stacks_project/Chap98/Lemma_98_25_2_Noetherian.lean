module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Whiskering
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf

/-!
# Locally Noetherian schemes over a base

The full subcategory of locally Noetherian objects of `Over S`, the induced
standard topology of the site `(Noetherian/S)_τ`, and restriction of
set-valued presheaves along the inclusion into `(Sch/S)_τ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.Scheme.Over

/-- Locally Noetherian schemes over a base scheme `S`. -/
def locallyNoetherian (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun X ↦ IsLocallyNoetherian X.left

/-- Membership in `locallyNoetherian S` is local Noetherianity of the
underlying scheme. -/
theorem locallyNoetherian_iff {S : Scheme.{u}} (X : Over S) :
    locallyNoetherian S X ↔ IsLocallyNoetherian X.left := sorry

end AlgebraicGeometry.Scheme.Over

namespace AlgebraicGeometry.StandardTopology

open Scheme.Over

/-- The Grothendieck topology of the site `(Noetherian/S)_τ`. -/
abbrev locallyNoetherianTopology (τ : StandardTopology) (S : Scheme.{u}) :
    GrothendieckTopology (locallyNoetherian S).FullSubcategory :=
  (locallyNoetherian S).ι.restrictedTopology (τ.overTopology S)

/-- `locallyNoetherianTopology τ S` is the restriction of `τ.overTopology S`
along the inclusion of locally Noetherian schemes over `S`. -/
theorem locallyNoetherianTopology_eq (τ : StandardTopology) (S : Scheme.{u}) :
    locallyNoetherianTopology τ S =
      (locallyNoetherian S).ι.restrictedTopology (τ.overTopology S) := sorry

/-- Restriction of a set-valued presheaf on `Over S` along the inclusion of
locally Noetherian schemes over `S`. -/
def restrictPresheaf (S : Scheme.{u}) :
    ((Over S)ᵒᵖ ⥤ Type (u + 1)) ⥤
      ((locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)) :=
  (Functor.whiskeringLeft _ _ _).obj (locallyNoetherian S).ι.op

/-- The object map of `restrictPresheaf` is precomposition with the opposite of
the inclusion of locally Noetherian schemes over `S`. -/
theorem restrictPresheaf_obj (S : Scheme.{u}) (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) :
    (restrictPresheaf S).obj F = (locallyNoetherian S).ι.op ⋙ F := sorry

end AlgebraicGeometry.StandardTopology
