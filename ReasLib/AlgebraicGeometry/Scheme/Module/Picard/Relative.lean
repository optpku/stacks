/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativePicard

/-- The presheaf on `S`-schemes sending `T` to the Picard group of `T ×ₛ X`. -/
noncomputable def presheaf {S : Scheme.{u}} (X : Over S) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := (T.unop ⊗ X).left.PicardGroup
  map g := TypeCat.ofHom (Scheme.Hom.picardPullback ((g.unop ▷ X).left))
  map_id := sorry
  map_comp := sorry

/-- Evaluation of the relative Picard presheaf at an `S`-scheme `T`. -/
theorem presheaf_obj {S : Scheme.{u}} (X T : Over S) :
    (presheaf X).obj (op T) = (T ⊗ X).left.PicardGroup := sorry

/-- The relative Picard functor is the fppf sheafification of the presheaf
`T ↦ Pic(T ×ₛ X)`. -/
noncomputable def functor {S : Scheme.{u}} (X : Over S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj (presheaf X)

/-- The underlying presheaf of the relative Picard functor is the fppf sheafification of
`presheaf X`. -/
theorem functor_val {S : Scheme.{u}} (X : Over S) :
    (functor X).obj = (Scheme.fppfTopology.over S).sheafify (presheaf X) := sorry

/-- A chosen `S`-scheme representing the relative Picard functor. -/
noncomputable def scheme {S : Scheme.{u}} (X : Over S)
    [(functor X).obj.IsRepresentable] : Over S :=
  (functor X).obj.reprX

/-- The chosen relative Picard scheme represents the relative Picard functor. -/
noncomputable def schemeRepresentation {S : Scheme.{u}} (X : Over S)
    [(functor X).obj.IsRepresentable] :
    (functor X).obj.RepresentableBy (scheme X) :=
  (functor X).obj.representableBy

end AlgebraicGeometry.RelativePicard
