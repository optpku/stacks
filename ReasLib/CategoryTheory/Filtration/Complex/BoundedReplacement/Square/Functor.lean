/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.GE.Functor
public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.LE.Functor
public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.Square

/-!
# Functorial bounded replacement squares

The canonical bounded vertex is the composite of upper and lower truncation functors.  Its two
comparison edges are natural transformations, so applications can map whole replacement squares
without reconstructing componentwise diagrams.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.Replace.Square.Bounded

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The map between canonical bounded vertices induced by a filtered cochain map. -/
@[stacks 05S5 "functorial filtered bounded replacement"]
noncomputable def map {K L : FilteredComplex A} (f : K ⟶ L) (a b : ℤ) :
    obj K a b ⟶ obj L a b :=
  TruncGE.map (TruncLE.map f b) a

/-- Canonical bounded replacement at fixed bounds is functorial. -/
@[stacks 05S5 "functorial filtered bounded replacement"]
noncomputable def functor (a b : ℤ) : FilteredComplex A ⥤ FilteredComplex A :=
  TruncLE.functor b ⋙ TruncGE.functor a

/-- Evaluating the bounded replacement functor gives the canonical bounded vertex. -/
@[simp, stacks 05S5]
theorem functor_obj (K : FilteredComplex A) (a b : ℤ) :
    (functor (A := A) a b).obj K = obj K a b := sorry

/-- The bounded replacement functor acts by the iterated truncation map. -/
@[simp, stacks 05S5]
theorem functor_map {K L : FilteredComplex A} (f : K ⟶ L) (a b : ℤ) :
    (functor (A := A) a b).map f = map f a b := sorry

/-- Bounded replacement maps preserve identities. -/
@[simp]
theorem map_id (K : FilteredComplex A) (a b : ℤ) :
    map (𝟙 K) a b = 𝟙 (obj K a b) := sorry

/-- Bounded replacement maps preserve composition. -/
@[simp]
theorem map_comp {K L M : FilteredComplex A} (f : K ⟶ L) (g : L ⟶ M)
    (a b : ℤ) : map (f ≫ g) a b = map f a b ≫ map g a b := sorry

/-- The edge from the upper truncation to the bounded vertex is natural. -/
@[reassoc, stacks 05S5]
theorem fromLE_naturality {K L : FilteredComplex A} (f : K ⟶ L) (a b : ℤ) :
    TruncLE.map f b ≫ fromLE L a b = fromLE K a b ≫ map f a b := sorry

/-- The edge from the bounded vertex to the lower truncation is natural. -/
@[reassoc, stacks 05S5]
theorem toGE_naturality {K L : FilteredComplex A} (f : K ⟶ L) (a b : ℤ) :
    map f a b ≫ toGE L a b = toGE K a b ≫ TruncGE.map f a := sorry

namespace FromLE

/-- Naturality of the upper-to-bounded edge in functorial form. -/
@[stacks 05S5]
theorem naturality {K L : FilteredComplex A} (f : K ⟶ L) (a b : ℤ) :
    (TruncLE.functor (A := A) b).map f ≫ fromLE L a b =
      fromLE K a b ≫ (functor (A := A) a b).map f := sorry

/-- The upper-to-bounded edges form a natural transformation. -/
@[stacks 05S5 "upper-to-bounded filtered replacement"]
noncomputable def natTrans (a b : ℤ) :
    TruncLE.functor (A := A) b ⟶ functor (A := A) a b where
  app K := fromLE K a b
  naturality := fun {K L} f ↦ naturality (A := A) (K := K) (L := L) f a b

/-- A component of the upper-to-bounded natural transformation is the canonical square edge. -/
@[simp, stacks 05S5]
theorem natTrans_app (K : FilteredComplex A) (a b : ℤ) :
    (natTrans (A := A) a b).app K = fromLE K a b := sorry

end FromLE

namespace ToGE

/-- Naturality of the bounded-to-lower edge in functorial form. -/
@[stacks 05S5]
theorem naturality {K L : FilteredComplex A} (f : K ⟶ L) (a b : ℤ) :
    (functor (A := A) a b).map f ≫ toGE L a b =
      toGE K a b ≫ (TruncGE.functor (A := A) a).map f := sorry

/-- The bounded-to-lower edges form a natural transformation. -/
@[stacks 05S5 "bounded-to-lower filtered replacement"]
noncomputable def natTrans (a b : ℤ) :
    functor (A := A) a b ⟶ TruncGE.functor (A := A) a where
  app K := toGE K a b
  naturality := fun {K L} f ↦ naturality (A := A) (K := K) (L := L) f a b

/-- A component of the bounded-to-lower natural transformation is the canonical square edge. -/
@[simp, stacks 05S5]
theorem natTrans_app (K : FilteredComplex A) (a b : ℤ) :
    (natTrans (A := A) a b).app K = toGE K a b := sorry

end ToGE

end CategoryTheory.FilteredComplex.Replace.Square.Bounded
