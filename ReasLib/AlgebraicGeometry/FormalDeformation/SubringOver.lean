/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal

/-!
# Subring-over categories of a functor to `ArtinianLocalAlgCat`

For `p : F ⥤ ArtinianLocalAlgCat Λ k` and an object `x` of `F`, the category `S_x` is
the full subcategory of `Over x` on arrows `x' ⟶ x` whose image under `p` is injective
on underlying `Λ`-algebra maps. An object is minimal when every incoming morphism of
`S_x` is an isomorphism.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- The object property on `Over x` of lying over an injective morphism of
`ArtinianLocalAlgCat`. -/
def isSubringOver (p : F ⥤ ArtinianLocalAlgCat Λ k) (x : F) : ObjectProperty (Over x) :=
  fun a => Function.Injective (p.map a.hom).hom

/-- The category `S_x` of arrows `x' ⟶ x` lying over a subring inclusion of `p.obj x`. -/
abbrev SubringOver (p : F ⥤ ArtinianLocalAlgCat Λ k) (x : F) :=
  (isSubringOver p x).FullSubcategory

namespace SubringOver

/-- Package an arrow `φ : left ⟶ x` lying over an injective base algebra map as an
object of `SubringOver p x`. -/
def mk {x left : F} {p : F ⥤ ArtinianLocalAlgCat Λ k} (φ : left ⟶ x)
    (h : Function.Injective (p.map φ).hom) : SubringOver p x where
  obj := Over.mk φ
  property := h

/-- The inclusion of `SubringOver p x` into `Over x`. -/
abbrev forget (p : F ⥤ ArtinianLocalAlgCat Λ k) (x : F) : SubringOver p x ⥤ Over x :=
  ObjectProperty.ι _

/-- The underlying arrow `x' ⟶ x` of an object of `SubringOver p x`. -/
abbrev arrow {p : F ⥤ ArtinianLocalAlgCat Λ k} {x : F} (a : SubringOver p x) : a.obj.left ⟶ x :=
  a.obj.hom

/-- The identity arrow of `x`, as an object of `SubringOver p x`. -/
def id (p : F ⥤ ArtinianLocalAlgCat Λ k) (x : F) : SubringOver p x :=
  mk (𝟙 x) sorry

/-- An object of `S_x` is a packaged arrow over `x` whose image under `p` is injective. -/
theorem spec {p : F ⥤ ArtinianLocalAlgCat Λ k} {x : F} (a : SubringOver p x) :
    Function.Injective (p.map (arrow a)).hom ∧ a.obj = Over.mk (arrow a) := sorry

/-- The packaged constructor recovers the supplied arrow. -/
theorem mk_arrow {x left : F} {p : F ⥤ ArtinianLocalAlgCat Λ k} (φ : left ⟶ x)
    (h : Function.Injective (p.map φ).hom) :
    arrow (mk φ h) = φ := sorry

/-- The forgetful functor sends an object of `SubringOver` to its underlying over-object. -/
theorem forget_obj {p : F ⥤ ArtinianLocalAlgCat Λ k} {x : F} (a : SubringOver p x) :
    (forget p x).obj a = a.obj := sorry

/-- An object of `S_x` is minimal when every incoming morphism of `S_x` is an isomorphism. -/
def IsMinimal {p : F ⥤ ArtinianLocalAlgCat Λ k} {x : F} (a : SubringOver p x) : Prop :=
  ∀ ⦃b : SubringOver p x⦄ (f : b ⟶ a), IsIso f

/-- Minimality is equivalent to every incoming morphism of `S_x` being an isomorphism. -/
theorem isMinimal_iff {p : F ⥤ ArtinianLocalAlgCat Λ k} {x : F} (a : SubringOver p x) :
    IsMinimal a ↔ ∀ ⦃b : SubringOver p x⦄ (f : b ⟶ a), IsIso f := sorry

/-- Incoming morphisms of `S_x` into a minimal object are isomorphisms. -/
theorem isMinimal_isIso {p : F ⥤ ArtinianLocalAlgCat Λ k} {x : F} {a : SubringOver p x}
    (ha : IsMinimal a) {b : SubringOver p x} (f : b ⟶ a) : IsIso f := sorry

/-- Minimal objects of `S_x` exist when `p` is cofibered in groupoids, since the base
algebra of `x` has finite length. -/
theorem exists_isMinimal (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x : F) : ∃ a : SubringOver p x, IsMinimal a := sorry

end SubringOver

end CategoryTheory.Functor
