module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Presheaf

/-!
# Relative Picard classes before sheafification

For every morphism `X → S`, the relative quotient presheaf sends `T → S` to
`Pic(T ×ₛ X) / image(Pic(T))`. It is distinct from the raw Picard presheaf and
from its fppf sheafification. No rational point or representability is assumed.

The projection from raw classes is explicit. Subsequent comparisons with
rigidified classes and fppf sheaves can therefore preserve this canonical map,
rather than identifying unrelated choices of representatives.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

noncomputable section
universe u

namespace AlgebraicGeometry.RelativePicard

/-- Classes pulled back from the test scheme, inside `Pic(T ×ₛ X)`. -/
noncomputable def baseClasses {S : Scheme.{u}} (X : Over S) (T : (Over S)ᵒᵖ) :
    AddSubgroup ((groupPresheaf X).obj T) :=
  (Scheme.Hom.picardPullback (CartesianMonoidalCategory.fst T.unop X).left).range

/-- Base classes remain base classes after a further base change. -/
theorem map_mem_baseClasses {S : Scheme.{u}} (X : Over S)
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') {a : (groupPresheaf X).obj T}
    (ha : a ∈ baseClasses X T) :
    (groupPresheaf X).map f a ∈ baseClasses X T' := by
  obtain ⟨b, rfl⟩ := ha
  refine ⟨Scheme.Hom.picardPullback f.unop.left b, ?_⟩
  change Scheme.Hom.picardPullback (pullback.fst T'.unop.hom X.hom)
      (Scheme.Hom.picardPullback f.unop.left b) =
    Scheme.Hom.picardPullback ((f.unop ▷ X).left)
      (Scheme.Hom.picardPullback (pullback.fst T.unop.hom X.hom) b)
  calc
    _ = Scheme.Hom.picardPullback
        (pullback.fst T'.unop.hom X.hom ≫ f.unop.left) b :=
      (Scheme.Hom.picardPullback_comp_apply _ _ b).symm
    _ = Scheme.Hom.picardPullback
        ((f.unop ▷ X).left ≫ pullback.fst T.unop.hom X.hom) b := by
      exact congrArg (fun z ↦ Scheme.Hom.picardPullback z b)
        (Over.whiskerRight_left_fst f.unop).symm
    _ = _ := Scheme.Hom.picardPullback_comp_apply _ _ b

/-- The quotient `Pic(T ×ₛ X) / image(Pic(T))`, retaining the group structure. -/
noncomputable def quotientPresheaf {S : Scheme.{u}} (X : Over S) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj T := AddCommGrpCat.of ((groupPresheaf X).obj T ⧸ baseClasses X T)
  map f := AddCommGrpCat.ofHom
    (QuotientAddGroup.map _ _ ((groupPresheaf X).map f).hom
      (fun _ ha ↦ map_mem_baseClasses X f ha))
  map_id T := by
    ext a
    change QuotientAddGroup.mk ((groupPresheaf X).map (𝟙 T) a) = QuotientAddGroup.mk a
    rw [(groupPresheaf X).map_id T]
    rfl
  map_comp f g := by
    ext a
    change QuotientAddGroup.mk ((groupPresheaf X).map (f ≫ g) a) =
      QuotientAddGroup.mk ((groupPresheaf X).map g ((groupPresheaf X).map f a))
    rw [(groupPresheaf X).map_comp f g]
    rfl

/-- The canonical projection from raw line-bundle classes to relative classes. -/
noncomputable def toQuotientPresheaf {S : Scheme.{u}} (X : Over S) :
    groupPresheaf X ⟶ quotientPresheaf X where
  app T := AddCommGrpCat.ofHom (QuotientAddGroup.mk' (baseClasses X T))
  naturality := by
    intro T T' f
    ext a
    rfl

/-- The projection on an individual class is the quotient map. -/
@[simp]
theorem toQuotientPresheaf_app {S : Scheme.{u}} (X : Over S)
    (T : (Over S)ᵒᵖ) (a : (groupPresheaf X).obj T) :
    (toQuotientPresheaf X).app T a = QuotientAddGroup.mk a := rfl

/-- Pullback of a relative class is represented by pullback of its line bundle. -/
@[simp]
theorem quotientPresheaf_map_mk {S : Scheme.{u}} (X : Over S)
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (a : (groupPresheaf X).obj T) :
    (quotientPresheaf X).map f (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk ((groupPresheaf X).map f a) := rfl

/-- Every relative class is represented by a line-bundle class on the base change. -/
theorem toQuotientPresheaf_app_surjective {S : Scheme.{u}} (X : Over S)
    (T : (Over S)ᵒᵖ) : Function.Surjective ((toQuotientPresheaf X).app T) :=
  QuotientAddGroup.mk_surjective

/-- A raw class vanishes in the relative quotient exactly when it comes from the test scheme. -/
@[simp]
theorem toQuotientPresheaf_app_eq_zero_iff {S : Scheme.{u}} (X : Over S)
    (T : (Over S)ᵒᵖ) (a : (groupPresheaf X).obj T) :
    (toQuotientPresheaf X).app T a = 0 ↔ a ∈ baseClasses X T :=
  QuotientAddGroup.eq_zero_iff a

end AlgebraicGeometry.RelativePicard
