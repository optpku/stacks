/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.GenericSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.MeromorphicSection.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Transfer

/-!
# First Chern classes of integral fundamental cycles

The divisor of a regular meromorphic section of an invertible module gives a
class in the canonical Chow group in degree one less than the dimension.
This class is independent of the section. The construction uses the generic
fibre of the module on a good integral algebraic space; extending it to more
general ringed sites requires corresponding cycle and Chow group theories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable [IsIntegral X]

/-- The subgroup of cycles of degree `dim_δ(X) - 1` on an integral algebraic space. -/
noncomputable abbrev codimOneCycleGroup :
    AddSubgroup (Function.locallyFinsupp (Points X) ℤ) :=
  cycleGroup f δ (deltaDimension f δ (univIrreducibleClosed X) - 1)

/-- The canonical Chow group in degree `dim_δ(X) - 1` on an integral algebraic space. -/
noncomputable abbrev codimOneChowGroup :=
  chowGroup f δ (deltaDimension f δ (univIrreducibleClosed X) - 1)

/-- The Chow class of a cycle of degree `dim_δ(X) - 1`, extended by zero to
locally finite cycles outside that degree subgroup. -/
noncomputable def chowClass (α : Function.locallyFinsupp (Points X) ℤ) :
    codimOneChowGroup f δ :=
  @dite (codimOneChowGroup f δ) (α ∈ codimOneCycleGroup f δ)
    (Classical.propDecidable _)
    (fun h ↦ chowMk f δ (deltaDimension f δ (univIrreducibleClosed X) - 1) ⟨α, h⟩)
    (fun _ ↦ 0)

/-- On cycles of degree `dim_δ(X) - 1`, the totalized Chow class is the
canonical quotient map. -/
theorem chowClass_eq_mk (α : Function.locallyFinsupp (Points X) ℤ)
    (hα : α ∈ codimOneCycleGroup f δ) :
    chowClass f δ α =
      chowMk f δ (deltaDimension f δ (univIrreducibleClosed X) - 1) ⟨α, hα⟩ := by
  simp only [chowClass, dif_pos hα]

/-- The generic point of the whole integral space is a generic point of an
irreducible component. -/
private theorem firstChernFundamental_generic_mem :
    genericPoint_of_good f (univIrreducibleClosed X) ∈ genericPoints X :=
  sorry

/-- The first Chern class of an invertible module capped with the fundamental
cycle, constructed as the Chow class of its generic meromorphic section divisor. -/
noncomputable def firstChernCapFundamental (L : X.Modules) [isInvertibleObject L] :
    codimOneChowGroup f δ :=
  let s := @MeromorphicConstruction.GenericSection.sectionValue S X inferInstance
    (IsQuasiSeparated.of_quasiSeparated f)
    (genericPoint_of_good f (univIrreducibleClosed X))
    (by exact firstChernFundamental_generic_mem f) L inferInstance
  let hs := @MeromorphicConstruction.GenericSection.sectionValue_regular S X inferInstance
    (IsQuasiSeparated.of_quasiSeparated f)
    (genericPoint_of_good f (univIrreducibleClosed X))
    (by exact firstChernFundamental_generic_mem f) L inferInstance
  chowMk f δ (deltaDimension f δ (univIrreducibleClosed X) - 1)
    ⟨meromorphicSectionDivisorCycle f δ s hs, meromorphicSectionDivisorCycle_mem f δ s hs⟩

/-- Divisor cycles of two regular meromorphic sections of the same invertible
module have the same class in the canonical Chow group. -/
theorem meromorphicSectionDivisorCycle_chowClass_eq {L : X.Modules}
    [isInvertibleObject L] (s t : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s) (ht : IsRegularMeromorphicSection X L t) :
    chowClass f δ (meromorphicSectionDivisorCycle f δ s hs) =
      chowClass f δ (meromorphicSectionDivisorCycle f δ t ht) :=
  sorry

/-- The first Chern class capped with the fundamental cycle equals the Chow
class of the divisor of any regular meromorphic section of the invertible module. -/
theorem firstChernCapFundamental_eq (L : X.Modules) [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s) :
    firstChernCapFundamental f δ L =
      chowClass f δ (meromorphicSectionDivisorCycle f δ s hs) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
