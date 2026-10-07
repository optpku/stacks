module

public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.LE

/-!
# Functorial upper truncation of filtered complexes

The universal lift makes good upper truncation functorial.  This leaf owns the map, functor,
inclusion natural transformation, and uniqueness API independently of the degreewise construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.TruncLE

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The map on good upper truncations induced by a filtered cochain map. -/
@[stacks 05S5 "functorial filtered upper truncation"]
noncomputable def map {K L : FilteredComplex A} (f : K ⟶ L) (b : ℤ) :
    truncLE K b ⟶ truncLE L b :=
  lift b (ιTruncLE K b ≫ f) (isStrictlyLE K b)

/-- A component of the induced upper-truncation map is the corresponding lift component. -/
@[simp, stacks 05S5]
theorem map_f {K L : FilteredComplex A} (f : K ⟶ L) (b n : ℤ) :
    (map f b).f n =
      liftComponent b (ιTruncLE K b ≫ f) (isStrictlyLE K b) n := sorry

/-- The canonical upper-truncation inclusions are natural. -/
@[reassoc, stacks 05S5]
theorem ι_naturality {K L : FilteredComplex A} (f : K ⟶ L) (b : ℤ) :
    map f b ≫ ιTruncLE L b = ιTruncLE K b ≫ f := sorry

/-- Upper truncation maps preserve identities. -/
@[simp]
theorem map_id (K : FilteredComplex A) (b : ℤ) :
    map (𝟙 K) b = 𝟙 (truncLE K b) := sorry

/-- Upper truncation maps preserve composition. -/
@[simp]
theorem map_comp {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M) (b : ℤ) :
    map (f ≫ g) b = map f b ≫ map g b := sorry

/-- Good upper truncation at a fixed cutoff is functorial. -/
@[stacks 05S5 "functorial filtered upper truncation"]
noncomputable def functor (b : ℤ) : FilteredComplex A ⥤ FilteredComplex A where
  obj K := truncLE K b
  map f := map f b
  map_id K := map_id K b
  map_comp f g := map_comp f g b

/-- Evaluating the upper-truncation functor gives good upper truncation. -/
@[simp, stacks 05S5]
theorem functor_obj (K : FilteredComplex A) (b : ℤ) :
    (functor (A := A) b).obj K = truncLE K b := sorry

/-- The upper-truncation functor acts on a morphism by the canonical lift. -/
@[simp, stacks 05S5]
theorem functor_map {K L : FilteredComplex A} (f : K ⟶ L) (b : ℤ) :
    (functor (A := A) b).map f = map f b := sorry

namespace Inclusion

/-- Naturality of upper-truncation inclusions in the shape required by a natural
transformation. -/
@[stacks 05S5]
theorem naturality {K L : FilteredComplex A} (f : K ⟶ L) (b : ℤ) :
    (functor (A := A) b).map f ≫ ιTruncLE L b =
      ιTruncLE K b ≫ (𝟭 (FilteredComplex A)).map f := sorry

/-- The canonical inclusions form a natural transformation from good upper truncation. -/
@[stacks 05S5 "inclusion from functorial filtered upper truncation"]
noncomputable def natTrans (b : ℤ) :
    functor (A := A) b ⟶ 𝟭 (FilteredComplex A) where
  app K := ιTruncLE K b
  naturality := fun {K L} f ↦ naturality (A := A) (K := K) (L := L) f b

/-- A component of the inclusion natural transformation is the canonical truncation map. -/
@[simp, stacks 05S5]
theorem natTrans_app (K : FilteredComplex A) (b : ℤ) :
    (natTrans (A := A) b).app K = ιTruncLE K b := sorry

end Inclusion

/-- A lift through upper truncation is uniquely determined by its composite with the canonical
inclusion. -/
@[stacks 05S5]
theorem lift_unique {L K : FilteredComplex A} (b : ℤ) (f : L ⟶ K)
    (hL : L.underlying.IsStrictlyLE b) (g : L ⟶ truncLE K b)
    (hg : g ≫ ιTruncLE K b = f) : g = lift b f hL := sorry

/-- Two maps from an upper-bounded complex into an upper truncation agree when their composites
with the canonical inclusion agree. -/
@[ext, stacks 05S5]
theorem hom_ext {L K : FilteredComplex A} (b : ℤ) (hL : L.underlying.IsStrictlyLE b)
    {f g : L ⟶ truncLE K b} (h : f ≫ ιTruncLE K b = g ≫ ιTruncLE K b) :
    f = g := sorry

/-- A map into upper truncation is the canonical lift exactly when it has the prescribed
composite with the inclusion. -/
@[stacks 05S5]
theorem lift_eq_iff {L K : FilteredComplex A} (b : ℤ) (f : L ⟶ K)
    (hL : L.underlying.IsStrictlyLE b) (g : L ⟶ truncLE K b) :
    lift b f hL = g ↔ g ≫ ιTruncLE K b = f := sorry

end CategoryTheory.FilteredComplex.TruncLE
