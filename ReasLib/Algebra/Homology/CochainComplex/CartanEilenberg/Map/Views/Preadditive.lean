module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Views.Naturality

/-!
# Additive computations for Cartan--Eilenberg map views

Columns, rows, bidegree terms, and the induced cycles/image/homology maps are all additive
projections of a resolution map.  This leaf exposes their computation rules without requiring
downstream files to unfold the underlying homological-complex constructions.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}

section Basic

/-- A column view sends the zero resolution map to zero. -/
@[simp, stacks 015J "zero column map of a Cartan-Eilenberg resolution"]
theorem column_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (p : ℤ) :
    column (zero : Map I J) p = 0 := sorry

/-- Column views preserve addition. -/
@[simp, stacks 015J "additive column map of a Cartan-Eilenberg resolution"]
theorem column_add (f g : Map I J) (p : ℤ) :
    column (f + g) p = column f p + column g p := sorry

/-- Column views preserve additive inverses. -/
@[simp]
theorem column_neg (f : Map I J) (p : ℤ) :
    column (-f) p = -column f p := sorry

/-- Column views preserve subtraction. -/
@[simp]
theorem column_sub (f g : Map I J) (p : ℤ) :
    column (f - g) p = column f p - column g p := sorry

/-- Column views preserve natural-number scalar multiplication. -/
@[simp]
theorem column_nsmul (n : ℕ) (f : Map I J) (p : ℤ) :
    column (n • f) p = n • column f p := sorry

/-- Column views preserve integer scalar multiplication. -/
@[simp]
theorem column_zsmul (n : ℤ) (f : Map I J) (p : ℤ) :
    column (n • f) p = n • column f p := sorry

/-- A row view sends the zero resolution map to zero. -/
@[simp, stacks 015J "zero row map of a Cartan-Eilenberg resolution"]
theorem row_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (q : ℤ) :
    row (zero : Map I J) q = 0 := sorry

/-- Row views preserve addition. -/
@[simp, stacks 015J "additive row map of a Cartan-Eilenberg resolution"]
theorem row_add (f g : Map I J) (q : ℤ) :
    row (f + g) q = row f q + row g q := sorry

/-- Row views preserve additive inverses. -/
@[simp]
theorem row_neg (f : Map I J) (q : ℤ) :
    row (-f) q = -row f q := sorry

/-- Row views preserve subtraction. -/
@[simp]
theorem row_sub (f g : Map I J) (q : ℤ) :
    row (f - g) q = row f q - row g q := sorry

/-- Row views preserve natural-number scalar multiplication. -/
@[simp]
theorem row_nsmul (n : ℕ) (f : Map I J) (q : ℤ) :
    row (n • f) q = n • row f q := sorry

/-- Row views preserve integer scalar multiplication. -/
@[simp]
theorem row_zsmul (n : ℤ) (f : Map I J) (q : ℤ) :
    row (n • f) q = n • row f q := sorry

/-- A bidegree term view sends the zero resolution map to zero. -/
@[simp, stacks 015J "zero bidegree map of a Cartan-Eilenberg resolution"]
theorem term_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (p q : ℤ) :
    term (zero : Map I J) p q = 0 := sorry

/-- Bidegree term views preserve addition. -/
@[simp, stacks 015J "additive bidegree map of a Cartan-Eilenberg resolution"]
theorem term_add (f g : Map I J) (p q : ℤ) :
    term (f + g) p q = term f p q + term g p q := sorry

/-- Bidegree term views preserve additive inverses. -/
@[simp]
theorem term_neg (f : Map I J) (p q : ℤ) :
    term (-f) p q = -term f p q := sorry

/-- Bidegree term views preserve subtraction. -/
@[simp]
theorem term_sub (f g : Map I J) (p q : ℤ) :
    term (f - g) p q = term f p q - term g p q := sorry

/-- Bidegree term views preserve natural-number scalar multiplication. -/
@[simp]
theorem term_nsmul (n : ℕ) (f : Map I J) (p q : ℤ) :
    term (n • f) p q = n • term f p q := sorry

/-- Bidegree term views preserve integer scalar multiplication. -/
@[simp]
theorem term_zsmul (n : ℤ) (f : Map I J) (p q : ℤ) :
    term (n • f) p q = n • term f p q := sorry

end Basic

section Homology

/-- Horizontal cycles maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero horizontal cycles map of a Cartan-Eilenberg resolution"]
theorem cyclesColumn_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (p : ℤ) :
    cyclesColumn (zero : Map I J) p = 0 := sorry

/-- Horizontal cycles maps preserve addition. -/
@[simp, stacks 015J "additive horizontal cycles map of a Cartan-Eilenberg resolution"]
theorem cyclesColumn_add (f g : Map I J) (p : ℤ) :
    cyclesColumn (f + g) p = cyclesColumn f p + cyclesColumn g p := sorry

/-- Horizontal cycles maps preserve additive inverses. -/
@[simp]
theorem cyclesColumn_neg (f : Map I J) (p : ℤ) :
    cyclesColumn (-f) p = -cyclesColumn f p := sorry

/-- Horizontal cycles maps preserve subtraction. -/
@[simp]
theorem cyclesColumn_sub (f g : Map I J) (p : ℤ) :
    cyclesColumn (f - g) p = cyclesColumn f p - cyclesColumn g p := sorry

/-- Horizontal cycles maps preserve natural-number scalar multiplication. -/
@[simp]
theorem cyclesColumn_nsmul (n : ℕ) (f : Map I J) (p : ℤ) :
    cyclesColumn (n • f) p = n • cyclesColumn f p := sorry

/-- Horizontal cycles maps preserve integer scalar multiplication. -/
@[simp]
theorem cyclesColumn_zsmul (n : ℤ) (f : Map I J) (p : ℤ) :
    cyclesColumn (n • f) p = n • cyclesColumn f p := sorry

/-- Horizontal image maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero horizontal image map of a Cartan-Eilenberg resolution"]
theorem imageColumn_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (p : ℤ) :
    imageColumn (zero : Map I J) p = 0 := sorry

/-- Horizontal image maps preserve addition. -/
@[simp, stacks 015J "additive horizontal image map of a Cartan-Eilenberg resolution"]
theorem imageColumn_add (f g : Map I J) (p : ℤ) :
    imageColumn (f + g) p = imageColumn f p + imageColumn g p := sorry

/-- Horizontal image maps preserve additive inverses. -/
@[simp]
theorem imageColumn_neg (f : Map I J) (p : ℤ) :
    imageColumn (-f) p = -imageColumn f p := sorry

/-- Horizontal image maps preserve subtraction. -/
@[simp]
theorem imageColumn_sub (f g : Map I J) (p : ℤ) :
    imageColumn (f - g) p = imageColumn f p - imageColumn g p := sorry

/-- Horizontal image maps preserve natural-number scalar multiplication. -/
@[simp]
theorem imageColumn_nsmul (n : ℕ) (f : Map I J) (p : ℤ) :
    imageColumn (n • f) p = n • imageColumn f p := sorry

/-- Horizontal image maps preserve integer scalar multiplication. -/
@[simp]
theorem imageColumn_zsmul (n : ℤ) (f : Map I J) (p : ℤ) :
    imageColumn (n • f) p = n • imageColumn f p := sorry

/-- Horizontal homology maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero horizontal homology map of a Cartan-Eilenberg resolution"]
theorem homologyColumn_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (p : ℤ) :
    homologyColumn (zero : Map I J) p = 0 := sorry

/-- Horizontal homology maps preserve addition. -/
@[simp, stacks 015J "additive horizontal homology map of a Cartan-Eilenberg resolution"]
theorem homologyColumn_add (f g : Map I J) (p : ℤ) :
    homologyColumn (f + g) p = homologyColumn f p + homologyColumn g p := sorry

/-- Horizontal homology maps preserve additive inverses. -/
@[simp]
theorem homologyColumn_neg (f : Map I J) (p : ℤ) :
    homologyColumn (-f) p = -homologyColumn f p := sorry

/-- Horizontal homology maps preserve subtraction. -/
@[simp]
theorem homologyColumn_sub (f g : Map I J) (p : ℤ) :
    homologyColumn (f - g) p = homologyColumn f p - homologyColumn g p := sorry

/-- Horizontal homology maps preserve natural-number scalar multiplication. -/
@[simp]
theorem homologyColumn_nsmul (n : ℕ) (f : Map I J) (p : ℤ) :
    homologyColumn (n • f) p = n • homologyColumn f p := sorry

/-- Horizontal homology maps preserve integer scalar multiplication. -/
@[simp]
theorem homologyColumn_zsmul (n : ℤ) (f : Map I J) (p : ℤ) :
    homologyColumn (n • f) p = n • homologyColumn f p := sorry

end Homology

end CochainComplex.CartanEilenbergResolution.Map
