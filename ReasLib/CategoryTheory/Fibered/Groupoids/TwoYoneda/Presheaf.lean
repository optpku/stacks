module

public import ReasLib.CategoryTheory.Comma.Over.Map
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Precomposition
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Yoneda.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Split

/-!
# The Cat-valued two-Yoneda presheaf

This file owns restriction on based slice-functor categories and its assembly into the
contravariant Cat-valued functor `TwoYoneda.presheaf`. The values are represented as categories
equipped with the property `IsGroupoid`, rather than by a chosen bundled inverse operation.
-/

@[expose] public section

universe v u vS uS

namespace CategoryTheory

open Opposite
open scoped BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]

namespace TwoYoneda

/-- Restriction `Mor_{Cat/C}(C/V, S) ⟶ Mor_{Cat/C}(C/U, S)` along `f : U ⟶ V`. Its data
are heterogeneous precomposition by the canonical slice morphism `BasedCategory.overMap f`. -/
def map (p : S ⥤ C) {U V : C} (f : U ⟶ V) :
    BasedCategory.Yoneda.hom p V ⥤ BasedCategory.Yoneda.hom p U :=
  BasedCategory.precomposition (BasedCategory.ofFunctor p) (BasedCategory.overMap f)

/-- Restriction along a slice morphism sends a based functor to its precomposition with the
canonical slice-change map. -/
@[simp]
theorem map.obj (p : S ⥤ C) {U V : C} (f : U ⟶ V) (G : BasedCategory.Yoneda.hom p V) :
    (map p f).obj G = BasedFunctor.comp (BasedCategory.overMap f) G := sorry

/-- Restriction along a slice morphism sends a based natural transformation to its left
whiskering by the canonical slice-change map. -/
@[simp]
theorem map.hom (p : S ⥤ C) {U V : C} (f : U ⟶ V)
    {G H : BasedCategory.Yoneda.hom p V} (η : G ⟶ H) :
    (map p f).map η = BasedCategory.whiskerLeft (BasedCategory.overMap f) η := sorry

/-- Restriction along an identity is the identity morphism in `Cat`. -/
theorem map.id (p : S ⥤ C) (U : Cᵒᵖ) :
    (map p (𝟙 U).unop).toCatHom =
      𝟙 (Cat.of (BasedCategory.Yoneda.hom p (unop U))) := sorry
/- Proof strategy: rewrite `Over.map (𝟙 _)` with `Over.mapId_eq`; use based-functor
extensionality, `BasedFunctor.id_comp`, and `BasedCategory.precomposition.map.id`. -/

/-- Restriction respects composition, with the order reversed by `Cᵒᵖ`. -/
theorem map.comp (p : S ⥤ C) {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) :
    (map p (f ≫ g).unop).toCatHom =
      (map p f.unop).toCatHom ≫ (map p g.unop).toCatHom := sorry
/- Proof strategy: rewrite `(f ≫ g).unop` and `Over.map` with `Over.mapComp_eq`; then use
`BasedFunctor.comp_assoc` and `BasedCategory.precomposition.map.comp`. -/

/-- The contravariant Cat-valued 2-Yoneda functor
`U ↦ Mor_{Cat/C}(C/U, S)`. Its values are canonically groupoidal when `p` is fibred in
groupoids; retaining that invariant property avoids choosing a bundled inverse operation. -/
def presheaf (p : S ⥤ C) : Cᵒᵖ ⥤ Cat where
  obj U := Cat.of (BasedCategory.Yoneda.hom p (unop U))
  map f := (TwoYoneda.map p f.unop).toCatHom
  map_id := map.id p
  map_comp := map.comp p

/-- The value of the `2`-Yoneda presheaf is the based-functor hom-category over the
corresponding slice. -/
@[simp]
theorem presheaf.obj (p : S ⥤ C) (U : Cᵒᵖ) :
    (presheaf p).obj U = Cat.of (BasedCategory.Yoneda.hom p (unop U)) := sorry

/-- The restriction map of the `2`-Yoneda presheaf is the Cat morphism underlying
heterogeneous based precomposition. -/
@[simp]
theorem presheaf.map (p : S ⥤ C) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (presheaf p).map f = (TwoYoneda.map p f.unop).toCatHom := sorry

/-- Every value of the 2-Yoneda presheaf is canonically a groupoid when `p` is fibred in
groupoids. -/
instance presheaf.isGroupoid
    (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] (U : Cᵒᵖ) :
    IsGroupoid ((presheaf p).obj U) := sorry
/- Proof strategy: unfold only `presheaf` at `U`; the goal is
`IsGroupoid (BasedCategory.Yoneda.hom p (unop U))`, supplied by the generic
`BasedFunctor.homGroupoid`. -/

end TwoYoneda

end CategoryTheory
