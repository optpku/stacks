/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.CategoryTheory.Homology.DoubleComplex.ProductTotal
public import ReasLib.CategoryTheory.Filtration.Complex.Functors
public import ReasLib.CategoryTheory.Filtration.Preadditive

/-!
# The product-tail filtration of a double complex

The decreasing filtration on the product total retains the antidiagonal entries whose
horizontal degree is at least the filtration index.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape
open scoped HomologicalComplex₂

noncomputable section

universe v u

namespace HomologicalComplex₂.ProductTotal

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCountableProducts C]

/-- The product `∏_{p+q=n, p ≥ i} A^{p,q}`. -/
def tail
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (n i : ℤ) :
    C :=
  ∏ᶜ fun p : {p : ℤ // i ≤ p} ↦ (K.X p.1).X (n - p.1)

/-- Projection from the product onto a retained bidegree. -/
def tail_π
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (n i : ℤ) (p : {p : ℤ // i ≤ p}) :
    tail K n i ⟶ (K.X p.1).X (n - p.1) :=
  Pi.π (fun q : {q : ℤ // i ≤ q} ↦ (K.X q.1).X (n - q.1)) p

/-- The complementary product of discarded antidiagonal summands `p < i`. -/
def complement
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (n i : ℤ) :
    C :=
  ∏ᶜ fun p : {p : ℤ // p < i} ↦ (K.X p.1).X (n - p.1)

/-- The canonical map `Tot^n_π(A) ⟶ ∏_{p+q=n, p < i} A^{p,q}`. -/
def complement_π
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (n i : ℤ) :
    (complex K).X n ⟶ complement K n i :=
  Pi.lift fun p ↦
    πOfEq K p.1 (n - p.1)
      ((add_comm p.1 (n - p.1)).trans (sub_add_cancel n p.1))

/-- Product-tail stages are antitone in the filtration index. -/
theorem filtration_monotone
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (n : ℤ) :
    Monotone fun p : ℤᵒᵈ ↦
      kernelSubobject (complement_π K n (OrderDual.ofDual p)) :=
  sorry

/-- Degree `n` of `Tot_π(A)` with the product-tail filtration
`F^i Tot^n = ker(Tot^n ⟶ ∏_{p < i} A^{p, n-p})`. -/
def filtrationObject
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) : FilteredObject C :=
  FilteredObject.mk ((complex K).X n)
    (OrderHom.mk
      (fun p ↦ kernelSubobject (complement_π K n (OrderDual.ofDual p)))
      (filtration_monotone K n))

/-- The total differential preserves every product-tail stage. -/
theorem filtration_d_preserves
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (a b p : ℤ) :
    ((filtrationObject K b).filtration.stage p).Factors
      (((filtrationObject K a).filtration.stage p).arrow ≫
        (complex K).d a b) :=
  sorry

/-- The product-tail filtered differential in total degree. -/
def filtration_d
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (a b : ℤ) :
    filtrationObject K a ⟶ filtrationObject K b :=
  FilteredObject.Hom.mk ((complex K).d a b) (filtration_d_preserves K a b)

/-- The product-tail differential vanishes off the cochain shape. -/
theorem filtration_d_shape
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (a b : ℤ) (hab : ¬ (up ℤ).Rel a b) :
    filtration_d K a b = 0 :=
  sorry

/-- Consecutive product-tail differentials compose to zero. -/
theorem filtration_d_comp
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (a b c : ℤ) (hab : (up ℤ).Rel a b) (hbc : (up ℤ).Rel b c) :
    filtration_d K a b ≫ filtration_d K b c = 0 :=
  sorry

/-- The filtered complex `Tot_π(A)` with product-tail stages
`F^i Tot^n_π(A) = ∏_{p+q=n, p ≥ i} A^{p,q}`. -/
def filtration
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    FilteredComplex C where
  X := filtrationObject K
  d := filtration_d K
  shape := filtration_d_shape K
  d_comp_d' := filtration_d_comp K

/-- Forgetting the product-tail filtration recovers `Tot_π(A)`. -/
theorem filtration_underlying
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    (filtration K).underlying = complex K :=
  rfl

/-- The filtration stage in total degree `n` is isomorphic to the product of retained antidiagonal entries
`∏_{p+q=n, p ≥ i} A^{p,q}`. -/
theorem filtration_stage_iso
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    (n i : ℤ) :
    IsIsomorphic (((filtration K).stage i).X n)
      (tail K n i) :=
  sorry

/-- A product-total map sends each product-tail stage into the corresponding target stage. -/
theorem filtrationMap_preserves
    {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L) (n p : ℤ) :
    ((filtrationObject L n).filtration.stage p).Factors
      (((filtrationObject K n).filtration.stage p).arrow ≫
        ((functor (C := C)).map f).f n) :=
  sorry

/-- The filtered map on product totals induced by a morphism of double complexes. -/
def filtrationMap
    {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L) :
    filtration K ⟶ filtration L where
  f n := FilteredObject.Hom.mk (((functor (C := C)).map f).f n)
    (filtrationMap_preserves f n)
  comm' a b hab := by
    apply FilteredObject.Hom.ext
    exact ((functor (C := C)).map f).comm a b

/-- The filtered product-total map preserves identity morphisms. -/
theorem filtrationMap_id (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    filtrationMap (𝟙 K) = 𝟙 (filtration K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply FilteredObject.Hom.ext
  exact congrArg (fun f ↦ f.f n) ((functor (C := C)).map_id K)

/-- The filtered product-total map preserves composition. -/
theorem filtrationMap_comp
    {K L M : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L) (g : L ⟶ M) :
    filtrationMap (f ≫ g) = filtrationMap f ≫ filtrationMap g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply FilteredObject.Hom.ext
  exact congrArg (fun f ↦ f.f n) ((functor (C := C)).map_comp f g)

/-- The functor taking a double complex to its product total with the product-tail filtration. -/
def filtrationFunctor :
    HomologicalComplex₂ C (up ℤ) (up ℤ) ⥤ FilteredComplex C where
  obj := filtration
  map := filtrationMap
  map_id := filtrationMap_id
  map_comp := filtrationMap_comp

end HomologicalComplex₂.ProductTotal
