/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Total.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalHomologyFunctor
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalFunctor.Preadditive

/-!
# Additive homology maps of Cartan--Eilenberg totals

This leaf exposes zero, additive, inverse, subtraction, and scalar computation for the homology
maps induced by total and filtered-total maps.  It also registers the corresponding homology
functors as additive, so downstream spectral-sequence arguments can use typeclass inference.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable {K L M : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}

/-- Mapped-total homology sends the zero resolution map to zero. -/
@[simp, stacks 015J "zero map on mapped-total homology"]
theorem mappedTotalHomology_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    mappedTotalHomology (zero : Map I J) F n = 0 := by
  have h : mappedTotal (zero : Map I J) F = 0 := by
    change HomologicalComplex₂.total.map
      ((F.mapHomologicalComplex₂ (up ℤ) (up ℤ)).map 0) (up ℤ) = 0
    rw [Functor.map_zero]
    ext q : 1
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    simp only [HomologicalComplex₂.ιTotal_map, HomologicalComplex.zero_f,
      CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]
  change HomologicalComplex.homologyMap _ n = _
  rw [h, HomologicalComplex.homologyMap_zero]

/-- Mapped-total homology preserves addition of resolution maps. -/
@[simp, stacks 015J "additive mapped-total homology map"]
theorem mappedTotalHomology_add (f g : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    mappedTotalHomology (f + g) F n =
      mappedTotalHomology f F n + mappedTotalHomology g F n := by
  have h : mappedTotal (f + g) F = mappedTotal f F + mappedTotal g F := by
    change HomologicalComplex₂.total.map
      ((F.mapHomologicalComplex₂ (up ℤ) (up ℤ)).map (f.hom + g.hom)) (up ℤ) =
      HomologicalComplex₂.total.map (mapped f F) (up ℤ) +
        HomologicalComplex₂.total.map (mapped g F) (up ℤ)
    rw [Functor.map_add]
    ext q : 1
    apply HomologicalComplex₂.total.hom_ext
    intro i j hij
    simp only [HomologicalComplex.add_f_apply, HomologicalComplex₂.ιTotal_map,
      Preadditive.comp_add, Preadditive.add_comp]
  change HomologicalComplex.homologyMap _ n = _
  rw [h, HomologicalComplex.homologyMap_add]

/-- Mapped-total homology preserves additive inverses. -/
@[simp]
theorem mappedTotalHomology_neg (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    mappedTotalHomology (-f) F n = -mappedTotalHomology f F n := by
  exact (AddMonoidHom.mk' (fun g : Map I J => mappedTotalHomology g F n)
    (fun g h => mappedTotalHomology_add g h F n)).map_neg f

/-- Mapped-total homology preserves subtraction. -/
@[simp]
theorem mappedTotalHomology_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    mappedTotalHomology (f - g) F n =
      mappedTotalHomology f F n - mappedTotalHomology g F n := by
  exact (AddMonoidHom.mk' (fun g : Map I J => mappedTotalHomology g F n)
    (fun g h => mappedTotalHomology_add g h F n)).map_sub f g

/-- Mapped-total homology preserves natural-number scalar multiplication. -/
@[simp]
theorem mappedTotalHomology_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive]
    (q : ℤ) :
    mappedTotalHomology (n • f) F q = n • mappedTotalHomology f F q := by
  exact (AddMonoidHom.mk' (fun g : Map I J => mappedTotalHomology g F q)
    (fun g h => mappedTotalHomology_add g h F q)).map_nsmul n f

/-- Mapped-total homology preserves integer scalar multiplication. -/
@[simp]
theorem mappedTotalHomology_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive]
    (q : ℤ) :
    mappedTotalHomology (n • f) F q = n • mappedTotalHomology f F q := by
  exact (AddMonoidHom.mk' (fun g : Map I J => mappedTotalHomology g F q)
    (fun g h => mappedTotalHomology_add g h F q)).map_zsmul n f

namespace First

/-- First-filtered total homology sends the zero resolution map to zero. -/
@[simp, stacks 015J "zero map on first-filtered total homology"]
theorem filteredTotalHomology_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (zero : Map I J) F n = 0 := by
  change mappedTotalHomology (zero : Map I J) F n = 0
  exact mappedTotalHomology_zero I J F n

/-- First-filtered total homology preserves addition. -/
@[simp, stacks 015J "additive first-filtered total homology map"]
theorem filteredTotalHomology_add (f g : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (f + g) F n =
      filteredTotalHomology f F n + filteredTotalHomology g F n := by
  change mappedTotalHomology (f + g) F n =
    mappedTotalHomology f F n + mappedTotalHomology g F n
  exact mappedTotalHomology_add f g F n

/-- First-filtered total homology preserves additive inverses. -/
@[simp]
theorem filteredTotalHomology_neg (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (-f) F n = -filteredTotalHomology f F n := by
  change mappedTotalHomology (-f) F n = -mappedTotalHomology f F n
  exact mappedTotalHomology_neg f F n

/-- First-filtered total homology preserves subtraction. -/
@[simp]
theorem filteredTotalHomology_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (f - g) F n =
      filteredTotalHomology f F n - filteredTotalHomology g F n := by
  change mappedTotalHomology (f - g) F n =
    mappedTotalHomology f F n - mappedTotalHomology g F n
  exact mappedTotalHomology_sub f g F n

/-- First-filtered total homology preserves natural-number scalar multiplication. -/
@[simp]
theorem filteredTotalHomology_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive]
    (q : ℤ) :
    filteredTotalHomology (n • f) F q = n • filteredTotalHomology f F q := by
  change mappedTotalHomology (n • f) F q = n • mappedTotalHomology f F q
  exact mappedTotalHomology_nsmul n f F q

/-- First-filtered total homology preserves integer scalar multiplication. -/
@[simp]
theorem filteredTotalHomology_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive]
    (q : ℤ) :
    filteredTotalHomology (n • f) F q = n • filteredTotalHomology f F q := by
  change mappedTotalHomology (n • f) F q = n • mappedTotalHomology f F q
  exact mappedTotalHomology_zsmul n f F q

end First

namespace Second

/-- Second-filtered total homology sends the zero resolution map to zero. -/
@[simp, stacks 015J "zero map on second-filtered total homology"]
theorem filteredTotalHomology_zero (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (zero : Map I J) F n = 0 := by
  change mappedTotalHomology (zero : Map I J) F n = 0
  exact mappedTotalHomology_zero I J F n

/-- Second-filtered total homology preserves addition. -/
@[simp, stacks 015J "additive second-filtered total homology map"]
theorem filteredTotalHomology_add (f g : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (f + g) F n =
      filteredTotalHomology f F n + filteredTotalHomology g F n := by
  change mappedTotalHomology (f + g) F n =
    mappedTotalHomology f F n + mappedTotalHomology g F n
  exact mappedTotalHomology_add f g F n

/-- Second-filtered total homology preserves additive inverses. -/
@[simp]
theorem filteredTotalHomology_neg (f : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (-f) F n = -filteredTotalHomology f F n := by
  change mappedTotalHomology (-f) F n = -mappedTotalHomology f F n
  exact mappedTotalHomology_neg f F n

/-- Second-filtered total homology preserves subtraction. -/
@[simp]
theorem filteredTotalHomology_sub (f g : Map I J) (F : A ⥤ B) [F.Additive] (n : ℤ) :
    filteredTotalHomology (f - g) F n =
      filteredTotalHomology f F n - filteredTotalHomology g F n := by
  change mappedTotalHomology (f - g) F n =
    mappedTotalHomology f F n - mappedTotalHomology g F n
  exact mappedTotalHomology_sub f g F n

/-- Second-filtered total homology preserves natural-number scalar multiplication. -/
@[simp]
theorem filteredTotalHomology_nsmul (n : ℕ) (f : Map I J) (F : A ⥤ B) [F.Additive]
    (q : ℤ) :
    filteredTotalHomology (n • f) F q = n • filteredTotalHomology f F q := by
  change mappedTotalHomology (n • f) F q = n • mappedTotalHomology f F q
  exact mappedTotalHomology_nsmul n f F q

/-- Second-filtered total homology preserves integer scalar multiplication. -/
@[simp]
theorem filteredTotalHomology_zsmul (n : ℤ) (f : Map I J) (F : A ⥤ B) [F.Additive]
    (q : ℤ) :
    filteredTotalHomology (n • f) F q = n • filteredTotalHomology f F q := by
  change mappedTotalHomology (n • f) F q = n • mappedTotalHomology f F q
  exact mappedTotalHomology_zsmul n f F q

end Second

end CochainComplex.CartanEilenbergResolution.Map

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- Mapped-total homology is an additive functor in the resolution. -/
@[stacks 015J "additivity of mapped-total homology"]
noncomputable instance mappedTotalHomology_additive (F : A ⥤ B) [F.Additive] (n : ℤ) :
    (mappedTotalHomology F n).Additive := by
  constructor
  intro X Y f g
  exact Map.mappedTotalHomology_add f g F n

namespace First

/-- First-filtered total homology is an additive functor in the resolution. -/
@[stacks 015J "additivity of first-filtered total homology"]
noncomputable instance filteredTotalHomology_additive (F : A ⥤ B) [F.Additive] (n : ℤ) :
    (filteredTotalHomology F n).Additive := by
  constructor
  intro X Y f g
  exact Map.First.filteredTotalHomology_add f g F n

end First

namespace Second

/-- Second-filtered total homology is an additive functor in the resolution. -/
@[stacks 015J "additivity of second-filtered total homology"]
noncomputable instance filteredTotalHomology_additive (F : A ⥤ B) [F.Additive] (n : ℤ) :
    (filteredTotalHomology F n).Additive := by
  constructor
  intro X Y f g
  exact Map.Second.filteredTotalHomology_add f g F n

end Second

#synth (mappedTotalHomology (A := A) (B := A) (𝟭 A) 0).Additive

end CochainComplex.CartanEilenbergResolution.Bundled
