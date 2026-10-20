/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Definition

/-!
# Views of maps of Cartan--Eilenberg resolutions

A map of Cartan--Eilenberg resolutions induces maps on its columns, rows, bidegree terms,
horizontal cycles, horizontal images, and horizontal homology.  This file records those views
and their component, identity, and composition API.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L M : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}

/-- The column map in horizontal degree `p`. -/
@[stacks 015J "column of a Cartan-Eilenberg resolution map"]
abbrev column (f : Map I J) (p : ℤ) : I.column p ⟶ J.column p :=
  f.hom.f p

/-- The row map in vertical degree `q`. -/
@[stacks 015J "row of a Cartan-Eilenberg resolution map"]
abbrev row (f : Map I J) (q : ℤ) : I.row q ⟶ J.row q :=
  ((flipFunctor A (up ℤ) (up ℤ)).map f.hom).f q

/-- The map on the bidegree `(p, q)` term. -/
@[stacks 015J "bidegree component of a Cartan-Eilenberg resolution map"]
abbrev term (f : Map I J) (p q : ℤ) : I.term p q ⟶ J.term p q :=
  (f.hom.f p).f q

/-- Evaluating a column map in vertical degree `q` gives the corresponding bidegree map. -/
@[simp, stacks 015J "component of a Cartan-Eilenberg column map"]
theorem column_f (f : Map I J) (p q : ℤ) :
    (column f p).f q = term f p q := sorry

/-- Evaluating a row map in horizontal degree `p` gives the corresponding bidegree map. -/
@[simp, stacks 015J "component of a Cartan-Eilenberg row map"]
theorem row_f (f : Map I J) (p q : ℤ) :
    (row f q).f p = term f p q := sorry

/-- The induced map between the horizontal cycles columns. -/
@[stacks 015J "cycles-column map of a Cartan-Eilenberg resolution map"]
noncomputable abbrev cyclesColumn (f : Map I J) (p : ℤ) :
    I.cyclesColumn p ⟶ J.cyclesColumn p :=
  HomologicalComplex.cyclesMap f.hom p

/-- The induced map between the horizontal differential-image columns. -/
@[stacks 015J "image-column map of a Cartan-Eilenberg resolution map"]
noncomputable abbrev imageColumn (f : Map I J) (p : ℤ) :
    I.imageColumn p ⟶ J.imageColumn p :=
  HomologicalComplex.imageMap f.hom p (p + 1)

/-- The induced map between the horizontal-homology columns. -/
@[stacks 015J "homology-column map of a Cartan-Eilenberg resolution map"]
noncomputable abbrev homologyColumn (f : Map I J) (p : ℤ) :
    I.homologyColumn p ⟶ J.homologyColumn p :=
  HomologicalComplex.homologyMap f.hom p

/-- The column of an identity resolution map is the identity. -/
@[simp]
theorem column_id (I : CartanEilenbergResolution K) (p : ℤ) :
    column (id I) p = 𝟙 (I.column p) := sorry

/-- The column of a composite resolution map is the composite of its column maps. -/
@[simp, reassoc]
theorem column_comp (f : Map I J) (g : Map J N) (p : ℤ) :
    column (comp f g) p = column f p ≫ column g p := sorry

/-- The row of an identity resolution map is the identity. -/
@[simp]
theorem row_id (I : CartanEilenbergResolution K) (q : ℤ) :
    row (id I) q = 𝟙 (I.row q) := sorry

/-- The row of a composite resolution map is the composite of its row maps. -/
@[simp, reassoc]
theorem row_comp (f : Map I J) (g : Map J N) (q : ℤ) :
    row (comp f g) q = row f q ≫ row g q := sorry

/-- Every bidegree component of an identity resolution map is the identity. -/
@[simp]
theorem term_id (I : CartanEilenbergResolution K) (p q : ℤ) :
    term (id I) p q = 𝟙 (I.term p q) := sorry

/-- The bidegree component of a composite is the composite of the bidegree components. -/
@[simp, reassoc]
theorem term_comp (f : Map I J) (g : Map J N) (p q : ℤ) :
    term (comp f g) p q = term f p q ≫ term g p q := sorry

/-- The induced map on horizontal cycles columns preserves identity maps. -/
@[simp]
theorem cyclesColumn_id (I : CartanEilenbergResolution K) (p : ℤ) :
    cyclesColumn (id I) p = 𝟙 (I.cyclesColumn p) := sorry

/-- The induced map on horizontal cycles columns preserves composition. -/
@[simp, reassoc]
theorem cyclesColumn_comp (f : Map I J) (g : Map J N) (p : ℤ) :
    cyclesColumn (comp f g) p = cyclesColumn f p ≫ cyclesColumn g p := sorry

/-- The induced map on horizontal differential-image columns preserves identity maps. -/
@[simp]
theorem imageColumn_id (I : CartanEilenbergResolution K) (p : ℤ) :
    imageColumn (id I) p = 𝟙 (I.imageColumn p) := sorry

/-- The induced map on horizontal differential-image columns preserves composition. -/
@[simp, reassoc]
theorem imageColumn_comp (f : Map I J) (g : Map J N) (p : ℤ) :
    imageColumn (comp f g) p = imageColumn f p ≫ imageColumn g p := sorry

/-- The induced map on horizontal-homology columns preserves identity maps. -/
@[simp]
theorem homologyColumn_id (I : CartanEilenbergResolution K) (p : ℤ) :
    homologyColumn (id I) p = 𝟙 (I.homologyColumn p) := sorry

/-- The induced map on horizontal-homology columns preserves composition. -/
@[stacks 015J "composition law for Cartan-Eilenberg homology-column maps", simp, reassoc]
theorem homologyColumn_comp (f : Map I J) (g : Map J N) (p : ℤ) :
    homologyColumn (comp f g) p = homologyColumn f p ≫ homologyColumn g p := sorry

end CochainComplex.CartanEilenbergResolution.Map
