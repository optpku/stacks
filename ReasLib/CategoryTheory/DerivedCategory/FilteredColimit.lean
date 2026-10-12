/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Filtered colimits of derived Hom-sets

@stack 0DHX

The derived-category computations used in filtered base-change arguments usually produce a
concrete cocone of stage Hom-sets.  This leaf records the reusable set-level comparison once and
for all.  It has no ring, tensor, or model assumptions: a chapter supplies the stage diagram, its
map to the target Hom-set, and the `IsColimit` certificate.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.DerivedCategory.FilteredColimit

variable {I : Type v} [Category.{w} I]

/-- Naturality of the explicit stage maps used by `mkCocone`. -/
@[stacks 0DHX "filtered Hom cocone naturality"]
theorem mkCocone_naturality (F : I ⥤ Type u) (T : Type u)
    (ι : ∀ i : I, F.obj i → T)
    (hι : ∀ ⦃i j : I⦄ (f : i ⟶ j) (x : F.obj i),
      ι j (F.map f x) = ι i x)
    {i j : I} (f : i ⟶ j) :
    F.map f ≫ TypeCat.ofHom (ι j) =
      TypeCat.ofHom (ι i) ≫ ((Functor.const I).obj T).map f := sorry

/-- Build a `Type`-valued cocone from its stage maps and the elementwise naturality law. -/
@[stacks 0DHX "filtered Hom cocone constructor"]
def mkCocone (F : I ⥤ Type u) (T : Type u)
    (ι : ∀ i : I, F.obj i → T)
    (hι : ∀ ⦃i j : I⦄ (f : i ⟶ j) (x : F.obj i),
      ι j (F.map f x) = ι i x) : Cocone F where
  pt := T
  ι :=
    { app := fun i => TypeCat.ofHom (ι i)
      naturality := fun {_ _} f => mkCocone_naturality F T ι hι f }

/-- A concrete filtered-colimit presentation of a target Hom-set.

`ι` is the actual map from each stage, while `isColimit` is the only deferred law.  Keeping the
map as a field makes this package usable for derived Homs whose target is not definitionally the
chosen categorical colimit object.
-/
@[stacks 0DHX "filtered Hom comparison data"]
structure HomComparison (F : I ⥤ Type u) (T : Type u) where
  /-- The canonical map from each stage into the target Hom-set. -/
  ι : ∀ i : I, F.obj i → T
  /-- Compatibility of the stage maps with every transition morphism. -/
  natural : ∀ ⦃i j : I⦄ (f : i ⟶ j) (x : F.obj i),
    ι j (F.map f x) = ι i x
  /-- The stage maps exhibit the target as the filtered colimit. -/
  isColimit : IsColimit (mkCocone F T ι natural)

namespace HomComparison

variable {F : I ⥤ Type u} {T : Type u} (h : HomComparison F T)

/-- The cocone underlying a concrete Hom comparison. -/
@[stacks 0DHX "the concrete filtered Hom cocone"]
abbrev cocone : Cocone F := mkCocone F T h.ι h.natural

section

variable [IsFilteredOrEmpty I]

/-- Every target morphism is represented at one stage. -/
@[stacks 0DHX "filtered Hom factorization"]
theorem factor (x : T) :
    ∃ (i : I) (y : F.obj i), x = h.ι i y := sorry

/-- Two representatives from one stage that have the same target image agree eventually. -/
@[stacks 0DHX "eventual equality of stage Hom representatives"]
theorem eventually_eq {i : I} (x y : F.obj i)
    (hx : h.ι i x = h.ι i y) :
    ∃ (j : I) (f : i ⟶ j), F.map f x = F.map f y := sorry

/-- Representatives from arbitrary stages are equal exactly when they agree at a common stage. -/
@[stacks 0DHX "filtered Hom representative equality criterion"]
theorem eq_iff {i j : I} (x : F.obj i) (y : F.obj j) :
    h.ι i x = h.ι j y ↔
      ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := sorry

end

/-- Naturality of the stage-to-target maps, exposed in elementwise form. -/
@[simp, stacks 0DHX "naturality of the concrete filtered Hom cocone"]
theorem ι_map {i j : I} (f : i ⟶ j) (x : F.obj i) :
    h.ι j (F.map f x) = h.ι i x := h.natural f x

end HomComparison

end CategoryTheory.DerivedCategory.FilteredColimit
