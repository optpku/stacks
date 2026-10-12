/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Functor
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Preadditive

/-!
# Additive computations for mapped Cartan--Eilenberg maps

Applying an additive functor termwise to a resolution map is itself additive.  This leaf exposes
the zero/additive/inverse/subtraction/scalar rules for the mapped double-complex and row views and
registers the bundled mapped-bicomplex functor as additive.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]
variable {K L : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}

/-- The mapped double-complex view sends the zero resolution map to zero. -/
@[simp, stacks 015J "zero mapped Cartan-Eilenberg map"]
theorem mapped_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] :
    mapped (zero : Map I J) F = 0 := sorry

/-- The mapped double-complex view preserves addition. -/
@[simp, stacks 015J "additive mapped Cartan-Eilenberg map"]
theorem mapped_add (f g : Map I J) (F : A ⥤ B) [F.Additive] :
    mapped (f + g) F = mapped f F + mapped g F := sorry

/-- The mapped double-complex view preserves additive inverses. -/
@[simp]
theorem mapped_neg (f : Map I J) (F : A ⥤ B) [F.Additive] :
    mapped (-f) F = -mapped f F := sorry

/-- The mapped double-complex view preserves subtraction. -/
@[simp]
theorem mapped_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] :
    mapped (f - g) F = mapped f F - mapped g F := sorry

/-- The mapped double-complex view preserves natural-number scalar multiplication. -/
@[simp]
theorem mapped_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive] :
    mapped (n • f) F = n • mapped f F := sorry

/-- The mapped double-complex view preserves integer scalar multiplication. -/
@[simp]
theorem mapped_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive] :
    mapped (n • f) F = n • mapped f F := sorry

/-- The mapped row view sends the zero resolution map to zero. -/
@[simp, stacks 015J "zero mapped row of a Cartan-Eilenberg resolution"]
theorem mappedRow_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    mappedRow (zero : Map I J) F q = 0 := sorry

/-- The mapped row view preserves addition. -/
@[simp, stacks 015J "additive mapped row of a Cartan-Eilenberg resolution"]
theorem mappedRow_add (f g : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    mappedRow (f + g) F q = mappedRow f F q + mappedRow g F q := sorry

/-- The mapped row view preserves additive inverses. -/
@[simp]
theorem mappedRow_neg (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    mappedRow (-f) F q = -mappedRow f F q := sorry

/-- The mapped row view preserves subtraction. -/
@[simp]
theorem mappedRow_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    mappedRow (f - g) F q = mappedRow f F q - mappedRow g F q := sorry

/-- The mapped row view preserves natural-number scalar multiplication. -/
@[simp]
theorem mappedRow_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    mappedRow (n • f) F q = n • mappedRow f F q := sorry

/-- The mapped row view preserves integer scalar multiplication. -/
@[simp]
theorem mappedRow_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive] (q : ℤ) :
    mappedRow (n • f) F q = n • mappedRow f F q := sorry

end CochainComplex.CartanEilenbergResolution.Map

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]

/-- The bundled mapped-bicomplex functor is additive. -/
@[stacks 015J "additivity of the mapped Cartan-Eilenberg bicomplex functor"]
noncomputable instance mapBicomplex_additive (F : A ⥤ B) [F.Additive] :
    (mapBicomplex F).Additive := sorry

/-- The bundled mapped-bicomplex functor preserves zero morphisms. -/
@[simp]
theorem mapBicomplex_map_zero (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} :
    (mapBicomplex F).map (0 : X ⟶ Y) = 0 := sorry

/-- The bundled mapped-bicomplex functor preserves sums of morphisms. -/
@[simp]
theorem mapBicomplex_map_add (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (f g : X ⟶ Y) :
    (mapBicomplex F).map (f + g) =
      (mapBicomplex F).map f + (mapBicomplex F).map g := sorry

/-- The bundled mapped-bicomplex functor preserves additive inverses. -/
@[simp]
theorem mapBicomplex_map_neg (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (f : X ⟶ Y) :
    (mapBicomplex F).map (-f) = -(mapBicomplex F).map f := sorry

/-- The bundled mapped-bicomplex functor preserves subtraction. -/
@[simp]
theorem mapBicomplex_map_sub (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (f g : X ⟶ Y) :
    (mapBicomplex F).map (f - g) =
      (mapBicomplex F).map f - (mapBicomplex F).map g := sorry

/-- The bundled mapped-bicomplex functor preserves natural-number scalar multiplication. -/
theorem mapBicomplex_map_nsmul (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (n : ℕ) (f : X ⟶ Y) :
    (mapBicomplex F).map (n • f) = n • (mapBicomplex F).map f := sorry

/-- The bundled mapped-bicomplex functor preserves integer scalar multiplication. -/
theorem mapBicomplex_map_zsmul (F : A ⥤ B) [F.Additive]
    {X Y : Bundled A} (n : ℤ) (f : X ⟶ Y) :
    (mapBicomplex F).map (n • f) = n • (mapBicomplex F).map f := sorry

#synth (mapBicomplex (A := A) (B := A) (𝟭 A)).Additive

end CochainComplex.CartanEilenbergResolution.Bundled
