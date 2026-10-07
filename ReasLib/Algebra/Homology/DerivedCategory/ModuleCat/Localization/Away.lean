module

public import ReasLib.Algebra.Category.ModuleCat.Localization.Away
public import ReasLib.Algebra.Homology.DerivedCategory.Linear
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal localization in derived module categories

This file owns the lower-truncation criterion detected by localization away
from one element and the cone of scalar multiplication.

@stack 0H84
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalizationAway

variable {R : Type u} [CommRing R]

/-- The localization away from `f` of the degree-`i` homology of a derived
`R`-module. -/
@[stacks 0H84 "localized homology away from one element"]
abbrev homology (f : R) (i : ℤ) (M : DerivedCategory (ModuleCat R)) :
    ModuleCat (Localization.Away f) :=
  ModuleCat.of (Localization.Away f)
    (LocalizedModule.Away f ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj M))

/-- Stacks `0H84`, in arbitrary degree: if the homology of `M` below `n`
vanishes after localization away from `f`, and the cone of multiplication by
`f` lies in degrees `≥ n - 1`, then `M` lies in degrees `≥ n`. -/
@[stacks 0H84 "principal-localization criterion for a derived lower bound"]
theorem isGE_of_smul_cone
    {M X : DerivedCategory (ModuleCat R)} {f : R} {g : M ⟶ X}
    {δ : X ⟶ M⟦(1 : ℤ)⟧} {n : ℤ}
    (hT : Triangle.mk (f • 𝟙 M) g δ ∈
      distTriang (DerivedCategory (ModuleCat R)))
    (hAway : ∀ i : ℤ, i < n → IsZero (homology f i M))
    (hX : X.IsGE (n - 1)) :
    M.IsGE n := sorry

/-- The degree-zero specialization of `isGE_of_smul_cone`, kept as the direct
source-facing bridge for the principal-localization criterion. -/
@[stacks 0H84 "degree-zero principal-localization criterion"]
theorem isGE_zero_of_smul_cone
    {M X : DerivedCategory (ModuleCat R)} {f : R} {g : M ⟶ X}
    {δ : X ⟶ M⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (f • 𝟙 M) g δ ∈
      distTriang (DerivedCategory (ModuleCat R)))
    (hAway : ∀ i : ℤ, i < 0 → IsZero (homology f i M))
    (hX : X.IsGE (-1)) :
    M.IsGE 0 := sorry

end CategoryTheory.DerivedCategory.LocalizationAway
