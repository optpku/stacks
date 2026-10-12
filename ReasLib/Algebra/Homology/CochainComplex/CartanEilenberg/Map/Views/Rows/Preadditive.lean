/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Views.Rows

/-!
# Additive rowwise views of Cartan--Eilenberg resolution maps

The maps induced on row cycles, differential images, and homology preserve the additive
operations on resolution maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}

/-- Row-cycles maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero row-cycles map of a Cartan-Eilenberg resolution"]
theorem cyclesRow_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (q p : ℤ) :
    cyclesRow (zero : Map I J) q p = 0 := sorry

/-- Row-cycles maps preserve addition. -/
@[simp]
theorem cyclesRow_add (f g : Map I J) (q p : ℤ) :
    cyclesRow (f + g) q p = cyclesRow f q p + cyclesRow g q p := sorry

/-- Row-cycles maps preserve additive inverses. -/
@[simp]
theorem cyclesRow_neg (f : Map I J) (q p : ℤ) :
    cyclesRow (-f) q p = -cyclesRow f q p := sorry

/-- Row-cycles maps preserve subtraction. -/
@[simp]
theorem cyclesRow_sub (f g : Map I J) (q p : ℤ) :
    cyclesRow (f - g) q p = cyclesRow f q p - cyclesRow g q p := sorry

/-- Row-cycles maps preserve natural-number scalar multiplication. -/
@[simp]
theorem cyclesRow_nsmul (n : ℕ) (f : Map I J) (q p : ℤ) :
    cyclesRow (n • f) q p = n • cyclesRow f q p := sorry

/-- Row-cycles maps preserve integer scalar multiplication. -/
@[simp]
theorem cyclesRow_zsmul (n : ℤ) (f : Map I J) (q p : ℤ) :
    cyclesRow (n • f) q p = n • cyclesRow f q p := sorry

/-- Row-image maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero row-image map of a Cartan-Eilenberg resolution"]
theorem imageRow_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (q p : ℤ) :
    imageRow (zero : Map I J) q p = 0 := sorry

/-- Row-image maps preserve addition. -/
@[simp]
theorem imageRow_add (f g : Map I J) (q p : ℤ) :
    imageRow (f + g) q p = imageRow f q p + imageRow g q p := sorry

/-- Row-image maps preserve additive inverses. -/
@[simp]
theorem imageRow_neg (f : Map I J) (q p : ℤ) :
    imageRow (-f) q p = -imageRow f q p := sorry

/-- Row-image maps preserve subtraction. -/
@[simp]
theorem imageRow_sub (f g : Map I J) (q p : ℤ) :
    imageRow (f - g) q p = imageRow f q p - imageRow g q p := sorry

/-- Row-image maps preserve natural-number scalar multiplication. -/
@[simp]
theorem imageRow_nsmul (n : ℕ) (f : Map I J) (q p : ℤ) :
    imageRow (n • f) q p = n • imageRow f q p := sorry

/-- Row-image maps preserve integer scalar multiplication. -/
@[simp]
theorem imageRow_zsmul (n : ℤ) (f : Map I J) (q p : ℤ) :
    imageRow (n • f) q p = n • imageRow f q p := sorry

/-- Row-homology maps send the zero resolution map to zero. -/
@[simp, stacks 015J "zero row-homology map of a Cartan-Eilenberg resolution"]
theorem homologyRow_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (q p : ℤ) :
    homologyRow (zero : Map I J) q p = 0 := sorry

/-- Row-homology maps preserve addition. -/
@[simp]
theorem homologyRow_add (f g : Map I J) (q p : ℤ) :
    homologyRow (f + g) q p = homologyRow f q p + homologyRow g q p := sorry

/-- Row-homology maps preserve additive inverses. -/
@[simp]
theorem homologyRow_neg (f : Map I J) (q p : ℤ) :
    homologyRow (-f) q p = -homologyRow f q p := sorry

/-- Row-homology maps preserve subtraction. -/
@[simp]
theorem homologyRow_sub (f g : Map I J) (q p : ℤ) :
    homologyRow (f - g) q p = homologyRow f q p - homologyRow g q p := sorry

/-- Row-homology maps preserve natural-number scalar multiplication. -/
@[simp]
theorem homologyRow_nsmul (n : ℕ) (f : Map I J) (q p : ℤ) :
    homologyRow (n • f) q p = n • homologyRow f q p := sorry

/-- Row-homology maps preserve integer scalar multiplication. -/
@[simp]
theorem homologyRow_zsmul (n : ℤ) (f : Map I J) (q p : ℤ) :
    homologyRow (n • f) q p = n • homologyRow f q p := sorry

end CochainComplex.CartanEilenbergResolution.Map
