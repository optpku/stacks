/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommRepresentationDuality
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.Algebra.Homology.Single

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u

namespace NoncommDualResolution
variable (R G : Type u) [Ring R] [Finite R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Actual dual terms AND reversed differentials, with compact right coefficients. -/
def chain {M : DiscreteModuleCat R G} (I : InjectiveResolution M) :
    ChainComplex (NoncommCompactRepresentation.Cat Rᵐᵒᵖ G) ℕ where
  X n := NoncommRepresentationDuality.dual R G (I.cocomplex.X n)
  d i j := NoncommRepresentationDuality.dualMap R G (I.cocomplex.d j i)
  shape := by sorry
  d_comp_d' := by sorry

/-- Dual of the specified degree-zero resolution inclusion. -/
def augmentation {M : DiscreteModuleCat R G} (I : InjectiveResolution M) :
    chain R G I ⟶ (ChainComplex.single₀ _).obj (NoncommRepresentationDuality.dual R G M) :=
  (ChainComplex.toSingle₀Equiv (chain R G I) _).symm
    ⟨NoncommRepresentationDuality.dualMap R G (I.ι.f 0), by sorry⟩

/-- Exactness of continuous character duality applies to this augmentation. -/
theorem augmentation_quasiIso {M : DiscreteModuleCat R G} (I : InjectiveResolution M) :
    QuasiIso (augmentation R G I) := by sorry

/-- Projectivity belongs to the compact ambient category, not finite modules. -/
def dualProjectiveResolution {M : DiscreteModuleCat R G} (I : InjectiveResolution M) :
    ProjectiveResolution (NoncommRepresentationDuality.dual R G M) where
  complex := chain R G I
  projective n := NoncommRepresentationDuality.dual_projective R G (I.cocomplex.X n)
  π := augmentation R G I
  quasiIso := augmentation_quasiIso R G I

/-- For any compact input, use ONLY its continuous bidual evaluation to attach
the actual dual complex to that input. -/
def compactResolution (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ G)
    (I : InjectiveResolution (NoncommRepresentationDuality.inverseDiscrete R G M)) :
    ProjectiveResolution M where
  complex := (dualProjectiveResolution R G I).complex
  projective := (dualProjectiveResolution R G I).projective
  π := (dualProjectiveResolution R G I).π ≫
    (ChainComplex.single₀ _).map (NoncommRepresentationDuality.compactEvaluationIso R G M).inv
  quasiIso := by sorry

/-- The ambient injective resolution gives a specified compact projective resolution. -/
def chosen (M : NoncommCompactRepresentation.Cat Rᵐᵒᵖ G) : ProjectiveResolution M :=
  compactResolution R G M
    (injectiveResolution (NoncommRepresentationDuality.inverseDiscrete R G M))

/-- Projective resolutions exist in the corrected compact category. -/
instance compact_hasProjectiveResolutions :
    HasProjectiveResolutions (NoncommCompactRepresentation.Cat Rᵐᵒᵖ G) where
  out M := ⟨⟨chosen R G M⟩⟩

end NoncommDualResolution
