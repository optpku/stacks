module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Theory
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section

open CategoryTheory
open scoped BigOperators

universe u

namespace AlgebraicGeometry.ChernClass.Theory

section Unit

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
variable (classes : Theory δ p) (E F : X.Modules) (r : ℕ)
variable [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
variable [hF : Scheme.Modules.IsFiniteLocallyFreeOfRank (r - 1) F]
variable (ι : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E) (q : E ⟶ F)
variable (hzero : ι ≫ q = 0) (hshort : (ShortComplex.mk ι q hzero).ShortExact)

include hE hF hshort

/-- In a short exact sequence `0 ⟶ 𝒪_X ⟶ E ⟶ F ⟶ 0` with `E` of rank `r`
and `F` of rank `r - 1`, the top Chern component of `E` vanishes. -/
theorem top_eq_zero_of_unit_shortExact : classes.component E r = 0 := sorry

/-- In a short exact sequence `0 ⟶ 𝒪_X ⟶ E ⟶ F ⟶ 0` with `E` of rank `r`
and `F` of rank `r - 1`, their Chern components agree in every degree below `r`. -/
theorem component_eq_of_unit_shortExact (j : ℕ) (hj : j < r) :
    classes.component E j = classes.component F j := sorry

end Unit

/-- For a short exact sequence `0 ⟶ L ⟶ E ⟶ F ⟶ 0` in which `L` is invertible
and `E`, `F` have ranks `r`, `r - 1`, the total Chern class of `E` is the product
of the total Chern classes of `L` and `F`. -/
theorem total_eq_mul_of_invertible_shortExact
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (L E F : X.Modules) (r : ℕ)
    [Scheme.Modules.Invertible L]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (r - 1) F]
    (ι : L ⟶ E) (q : E ⟶ F) (hzero : ι ≫ q = 0)
    (hshort : (ShortComplex.mk ι q hzero).ShortExact) :
    (∑ i : Fin (r + 1),
      ChernClass.homogeneous δ p (i : ℕ) (classes.component E i)) =
      (∑ i : Fin 2,
        ChernClass.homogeneous δ p (i : ℕ) (classes.component L i)) *
      (∑ i : Fin ((r - 1) + 1),
        ChernClass.homogeneous δ p (i : ℕ) (classes.component F i)) := sorry

/-- For a short exact complex whose first and third terms are finite locally free of
ranks `r₁` and `r₂`, the total Chern class of the middle term is the product of
the total Chern classes of the endpoint terms. -/
theorem total_eq_mul_of_shortExact
    {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : Theory δ p) (C : ShortComplex X.Modules) (r₁ r₂ : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r₁ C.X₁]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r₂ C.X₃]
    (hC : C.ShortExact) :
    (∑ i : Fin (r₁ + r₂ + 1),
      ChernClass.homogeneous δ p (i : ℕ) (classes.component C.X₂ i)) =
      (∑ i : Fin (r₁ + 1),
        ChernClass.homogeneous δ p (i : ℕ) (classes.component C.X₁ i)) *
      (∑ i : Fin (r₂ + 1),
        ChernClass.homogeneous δ p (i : ℕ) (classes.component C.X₃ i)) := sorry

end AlgebraicGeometry.ChernClass.Theory
