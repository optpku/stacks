/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Generation
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Regular
public import ReasLib.Algebra.Homology.DerivedCategory.Regular.HomologyGap
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Stage
public import ReasLib.RingTheory.RegularLocalRing.SerreCondition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strong generators of the perfect derived category

@stack 0FXH
@stack 0FXI
@stack 0FXL
@stack 0FXM

The degree-zero regular module strongly generates the perfect derived category exactly for
Noetherian regular rings of finite Krull dimension.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.ComposableArrows CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open DerivedCategory
open scoped CategoryTheory.ObjectProperty.GeneratedNotation ZeroObject

universe u

-- Local instance justification (search instability): ghost maps and the degree-zero embedding are
-- formed in the standard t-structure on the derived category of modules.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section Ghosts

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)

/-- Lemma 15.80.1 (0FXH): a chain of `n` cohomologically zero maps has zero composite on the
`n`th triangulated generation stage of `R[0]`. -/
@[stacks 0FXH "ghost composites on a generated stage"]
theorem ghost_composite_zero_of_mem_objectGeneratedStage
    {n : ℕ+} {X : ComposableArrows DMod n}
    (hX : (⟨(ModuleCat.single0 (ModuleCat.of R R))⟩[n]) X.left)
    (hghost : ∀ j : ℕ, (hj : j < n) → ∀ i : ℤ, (H i).map (X.arrow j hj).hom = 0) :
    X.hom = 0 := sorry

end Ghosts

section Noetherian

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Lemma 15.80.2 (0FXI): if `R[0]` strongly generates the perfect derived category, then `R`
is regular and has finite Krull dimension. -/
@[stacks 0FXI "strong generation implies regular finite dimension"]
theorem regularFiniteKrullDimension_of_ringSingleInPerfectDerived_isStrongGenerator
    (hstrong : ObjectProperty.IsStrongTriangulatedGenerator
      (ObjectProperty.singleton (ringSingleInPerfectDerived R))) :
    IsRegularRing R ∧ ∃ d : ℕ, Ring.KrullDimLE d R := sorry

/-- Proposition 15.80.6 (0FXM): regularity with finite Krull dimension, existence of a strong
generator, and strong generation by `R[0]` are equivalent. -/
@[stacks 0FXM "regular finite-dimensional rings and strong generators"]
theorem regularFiniteKrullDimension_tfae_perfectDerived_hasStrongGenerator_ringSingleStrongGenerator
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    List.TFAE
      [ IsRegularRing R ∧ ∃ d : ℕ, Ring.KrullDimLE d R,
        ∃ E : PerfectDerived R,
          ObjectProperty.IsStrongTriangulatedGenerator (ObjectProperty.singleton E),
        ObjectProperty.IsStrongTriangulatedGenerator
          (ObjectProperty.singleton (ringSingleInPerfectDerived R)) ] := sorry

end Noetherian

section Regular

variable {R : Type u} [CommRing R] [IsRegularRing R]

/-- Lemma 15.80.5 (0FXL): over a regular ring of finite Krull dimension, `R[0]` strongly
generates the perfect derived category. -/
@[stacks 0FXL "R[0] strongly generates the perfect derived category"]
theorem ringSingleInPerfectDerived_isStrongGenerator
    (hfinite : ∃ d : ℕ, Ring.KrullDimLE d R) :
    ObjectProperty.IsStrongTriangulatedGenerator
      (ObjectProperty.singleton (ringSingleInPerfectDerived R)) := sorry

end Regular

end CategoryTheory
