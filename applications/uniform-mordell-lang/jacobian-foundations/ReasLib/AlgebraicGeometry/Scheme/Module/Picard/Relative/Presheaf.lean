module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

/-!
# Picard classes on base changes

The additive group-valued presheaf `groupPresheaf` is the single owner of the
classes `Pic(T ×ₛ X)` and their pullbacks. The type-valued `presheaf` is its
forgetful view. Neither construction needs a field, a section, properness,
smoothness, or representability.

These are raw classes, before quotienting by line bundles from the test scheme.
`Relative.Quotient` exposes that quotient separately; `Relative` supplies fppf
sheafification. This distinction is useful for families, rigidification and
descent, independently of the existence of a Picard scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

noncomputable section
universe u

namespace AlgebraicGeometry.RelativePicard

/-- Picard groups of base changes, with tensor product written additively. -/
noncomputable def groupPresheaf {S : Scheme.{u}} (X : Over S) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj T := AddCommGrpCat.of (T.unop ⊗ X).left.PicardGroup
  map g := AddCommGrpCat.ofHom (Scheme.Hom.picardPullback ((g.unop ▷ X).left))
  map_id T := by
    ext a
    change Scheme.Hom.picardPullback (((𝟙 T).unop ▷ X).left) a = a
    simpa using Scheme.Hom.picardPullback_id_apply a
  map_comp f g := by
    ext a
    change Scheme.Hom.picardPullback ((((f ≫ g).unop) ▷ X).left) a =
      Scheme.Hom.picardPullback ((g.unop ▷ X).left)
        (Scheme.Hom.picardPullback ((f.unop ▷ X).left) a)
    rw [unop_comp, comp_whiskerRight, Over.comp_left]
    exact Scheme.Hom.picardPullback_comp_apply ((g.unop ▷ X).left)
      ((f.unop ▷ X).left) a


/-- The underlying sets of Picard classes on base changes. -/
noncomputable abbrev presheaf {S : Scheme.{u}} (X : Over S) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  groupPresheaf X ⋙ forget AddCommGrpCat

/-- The forgetful view adds no new Picard-class data. -/
noncomputable def groupPresheafForgetIso {S : Scheme.{u}} (X : Over S) :
    groupPresheaf X ⋙ forget AddCommGrpCat ≅ presheaf X :=
  Iso.refl _

/-- Evaluation of the raw Picard presheaf. -/
@[simp]
theorem presheaf_obj {S : Scheme.{u}} (X T : Over S) :
    (presheaf X).obj (op T) = (T ⊗ X).left.PicardGroup := rfl

/-- Pullback in the raw Picard presheaf is the ordinary Picard pullback. -/
@[simp]
theorem presheaf_map_apply {S : Scheme.{u}} (X : Over S)
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (a : (presheaf X).obj T) :
    (presheaf X).map f a = Scheme.Hom.picardPullback ((f.unop ▷ X).left) a := rfl

end AlgebraicGeometry.RelativePicard
