/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int

/-!
# Integer-indexed eta homology comparison

The divided-coordinate model identifies the class of a cycle in `K` with the class of the same
cycle in `eta f K`.  In the localization presentation of `eta`, this is the usual degree-`i`
scaling map; keeping divided coordinates makes the owner uniform for every `i : ℤ`.
@stack 0F7P
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex
open scoped nonZeroDivisors

noncomputable section

universe u v

namespace CochainComplex.BerthelotOgus.Int

variable {A : Type u} [CommRing A]

/-- Consecutive integer degrees are related by the cochain-complex shape. -/
theorem rel_succ (i : ℤ) : (ComplexShape.up ℤ).Rel i (i + 1) := sorry

/-- A cycle of `K` is an element of the corresponding divided-coordinate eta term. -/
theorem cycle_mem (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (x : K.cycles i) : (K.iCycles i).hom x ∈ term f K i := sorry

/-- The cycle inclusion into an integer eta term. -/
@[stacks 0F7P "cycle inclusion into the integer eta term"]
def cycleLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) :
    K.cycles i →ₗ[A] term f K i :=
  (K.iCycles i).hom.codRestrict _ (cycle_mem f K i)

/-- The cycle inclusion has zero composite with the divided eta differential. -/
theorem cycle_comp_d (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsTermwiseTorsionFree f K) (i : ℤ) :
    ModuleCat.ofHom (cycleLinear f K i) ≫ (eta f K hK).d i (i + 1) = 0 := sorry

/-- The cycle map from an object of the canonical regular domain to its integer-indexed eta
complex. -/
@[stacks 0F7P "cycle map into the integer eta complex"]
noncomputable def cyclesMap (f : A) (K : Domain f) (i : ℤ) :
    K.obj.cycles i ⟶ ((functor f).obj K).cycles i :=
  ((functor f).obj K).liftCycles'
    (ModuleCat.ofHom (cycleLinear f K.obj i)) (i + 1) (rel_succ i)
    (cycle_comp_d f K.obj K.property i)

/-- The cycle-level map into eta homology. -/
@[stacks 0F7P "cycle map into integer eta homology"]
noncomputable def cyclesToHomology (f : A) (K : Domain f) (i : ℤ) :
    K.obj.cycles i ⟶ ((functor f).obj K).homology i :=
  cyclesMap f K i ≫ ((functor f).obj K).homologyπ i

/-- Boundaries of the underlying complex map to zero in eta homology. -/
theorem boundaries_vanish (f : A) (K : Domain f) (i : ℤ) :
    (K.obj.sc i).toCycles ≫ cyclesToHomology f K i = 0 := sorry

/-- The map on homology induced by the cycle inclusion. -/
@[stacks 0F7P "homology map induced by the eta cycle inclusion"]
noncomputable def homologyMap (f : A) (K : Domain f) (i : ℤ) :
    K.obj.homology i ⟶ ((functor f).obj K).homology i :=
  (K.obj.sc i).descHomology (cyclesToHomology f K i) (boundaries_vanish f K i)

/-- The homology map is characterized on cycle representatives. -/
theorem homologyπ_comp_homologyMap
    (f : A) (K : Domain f) (i : ℤ) :
    K.obj.homologyπ i ≫ homologyMap f K i = cyclesToHomology f K i := sorry

/-- The integer eta homology map is natural on the canonical regular domain. -/
theorem homologyMap_naturality
    (f : A) {K L : Domain f} (φ : K ⟶ L) (i : ℤ) :
    homologyMap f K i ≫ HomologicalComplex.homologyMap ((functor f).map φ) i =
      HomologicalComplex.homologyMap φ.hom i ≫ homologyMap f L i := sorry

/-- Termwise `f`-regularity makes homology `f`-torsion map to zero under the eta comparison. -/
theorem torsionBy_le_ker
    (f : A) (K : Domain f) (i : ℤ) :
    Submodule.torsionBy A (K.obj.homology i) f ≤
      LinearMap.ker (homologyMap f K i).hom := sorry

/-- The canonical quotient comparison for an integer-indexed regular complex. -/
@[stacks 0F7P "integer-indexed Berthelot-Ogus eta homology comparison map"]
noncomputable def comparison (f : A) (K : Domain f) (i : ℤ) :
    ((K.obj.homology i) ⧸ Submodule.torsionBy A (K.obj.homology i) f) →ₗ[A]
      ((functor f).obj K).homology i :=
  (Submodule.torsionBy A (K.obj.homology i) f).liftQ
    (homologyMap f K i).hom
    (torsionBy_le_ker f K i)

/-- The quotient comparison sends a representative to its eta homology class. -/
theorem comparison_mk
    (f : A) (K : Domain f) (i : ℤ) (x : K.obj.homology i) :
    comparison f K i (Submodule.Quotient.mk x) = (homologyMap f K i).hom x := sorry

/-- The integer-indexed eta comparison is bijective on a termwise regular complex. -/
theorem comparison_bijective (f : A) (K : Domain f) (i : ℤ) :
    Function.Bijective (comparison f K i) := sorry

/-- The quotient comparison for a raw complex equipped with an explicit termwise regularity
proof.  Canonical downstream developments should use `comparison` on `Domain f`. -/
@[stacks 0F7P "eta homology comparison for an explicitly regular complex"]
noncomputable def comparisonOfRegular
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    ((K.homology i) ⧸ Submodule.torsionBy A (K.homology i) f) →ₗ[A]
      (eta f K hK).homology i :=
  comparison f ⟨K, hK⟩ i

/-- The raw regular-complex bridge is bijective. -/
theorem comparisonOfRegular_bijective
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    Function.Bijective (comparisonOfRegular f K i hK) := sorry

/-- Lemma 15.96.2, Tag 0F7P: for a nonzerodivisor `f` and an integer-indexed complex of
`f`-torsion-free modules, the degree-`i` divided-coordinate comparison identifies homology modulo
`f`-torsion with the homology of the Berthelot-Ogus eta complex. -/
@[stacks 0F7P "Berthelot-Ogus eta homology comparison"]
theorem comparison_bijective_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hf : f ∈ nonZeroDivisors A) (hK : IsTermwiseTorsionFree f K) :
    Function.Bijective (comparisonOfRegular f K i hK) := sorry

end CochainComplex.BerthelotOgus.Int
