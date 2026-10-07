module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Stupid

/-!
# Functoriality of the stupid filtration

The stupid filtration is canonical in a cochain complex.  This file supplies
the missing map and functor API, with the underlying cochain map left
unchanged in every degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Stupid

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A cochain map preserves the stupid filtration in each degree. -/
theorem mapComponent_preserves {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (p n : ℤ) :
    (stupidFiltrationSubobject L p n).Factors
      ((stupidFiltrationSubobject K p n).arrow ≫ f.f n) := sorry

/-- The filtered-object map in degree `n` induced by a cochain map. -/
def mapComponent {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (K.stupidFiltration).X n ⟶ (L.stupidFiltration).X n where
  hom := f.f n
  preserves := fun p ↦ mapComponent_preserves f p n

/-- Forgetting the filtration on a degree component recovers the original cochain-map
component. -/
@[simp]
theorem mapComponent_hom {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (mapComponent f n).hom = f.f n := sorry

/-- The filtered degree components induced by a cochain map commute with the differentials. -/
theorem mapComponent_comm {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    mapComponent f i ≫ (L.stupidFiltration).d i j =
      (K.stupidFiltration).d i j ≫ mapComponent f j := sorry

/-- A cochain map induces the canonical map of stupidly filtered complexes. -/
@[stacks 0D8Z]
def map {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    K.stupidFiltration ⟶ L.stupidFiltration where
  f := mapComponent f
  comm' := mapComponent_comm f

/-- The degree component of the map of stupid filtrations is the canonical filtered-object map. -/
@[simp, stacks 0D8Z]
theorem map_f {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (map f).f n = mapComponent f n := sorry

/-- Forgetting a map of stupid filtrations recovers the original cochain map. -/
@[simp, stacks 0D8Z]
theorem underlyingMap {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (K.stupidFiltration).underlyingMap (map f) = f := sorry

/-- The stupid-filtration map of an identity is the identity. -/
@[simp, stacks 0D8Z]
theorem map_id (K : CochainComplex A ℤ) : map (𝟙 K) = 𝟙 K.stupidFiltration := sorry

/-- Stupid-filtration maps preserve composition. -/
@[simp, stacks 0D8Z]
theorem map_comp {K L M : CochainComplex A ℤ} (f : K ⟶ L) (g : L ⟶ M) :
    map (f ≫ g) = map f ≫ map g := sorry

/-- Equipping a cochain complex with its stupid filtration is functorial. -/
@[stacks 0D8Z]
def functor : CochainComplex A ℤ ⥤ FilteredComplex A where
  obj := stupidFiltration
  map := map
  map_id := map_id
  map_comp := map_comp

/-- Evaluating the stupid-filtration functor equips a complex with its stupid filtration. -/
@[simp, stacks 0D8Z]
theorem functor_obj (K : CochainComplex A ℤ) :
    (functor (A := A)).obj K = K.stupidFiltration := sorry

/-- The map of the stupid-filtration functor is the canonical filtered map. -/
@[simp, stacks 0D8Z]
theorem functor_map {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (functor (A := A)).map f = map f := sorry

end CategoryTheory.CochainComplex.Stupid
