/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.AffineRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent.SmallSites
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.QuasiCoherent

/-!
# Affine derived sections of flat-fppf lower shriek

Derived lower shriek of a flat-fppf object with quasi-coherent cohomology
has invertible derived tensor comparison maps for every affine morphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ModulesOnCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/-- The derived affine sections of the lower-shriek image of flat-fppf
complexes with quasi-coherent cohomology. -/
abbrev restrictLowerShriekToAffine :
    DerivedQCohFlatFppf X ⥤
      RingedSite.Hom.ModuleDerived.{u + 1}
        (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X)) :=
  DerivedQCohFlatFppf.inclusion X ⋙
    flatFppfModuleLowerShriek.derived X ⋙ restrictToAffineDerived X

/-- Affine restriction of a lower-shriek image is computed by applying
derived lower shriek to the underlying flat-fppf derived object. -/
theorem restrictLowerShriekToAffine_obj (K : DerivedQCohFlatFppf X) :
    (restrictLowerShriekToAffine X).obj K =
      (restrictToAffineDerived X).obj
        ((flatFppfModuleLowerShriek.derived X).obj
          ((DerivedQCohFlatFppf.inclusion X).obj K)) := rfl

/-- For every morphism between affine objects of an algebraic stack, the
canonical derived tensor comparison map for the lower-shriek image of a
flat-fppf complex with quasi-coherent cohomology is an isomorphism. -/
@[stacks 0H15]
theorem flatFppfLowerShriek_affineComparison_isIso
    (K : DerivedQCohFlatFppf X) {x x' : affineSite X} (f : x ⟶ x') :
    IsIso
      ((chaoticComparison.{u + 1, u, u} (affineStructureSheaf X) f).app
        ((restrictLowerShriekToAffine X).obj K)) :=
  sorry

attribute [instance] flatFppfLowerShriek_affineComparison_isIso

/-- Derived affine restriction of lower shriek carries flat-fppf complexes
with quasi-coherent cohomology to the comparison-map quasi-coherent objects. -/
theorem flatFppfLowerShriek_mem_qcProperty (K : DerivedQCohFlatFppf X) :
    qcProperty X ((restrictLowerShriekToAffine X).obj K) := by
  apply (mem_QC_iff X _).2
  intro x x' f
  exact flatFppfLowerShriek_affineComparison_isIso X K f

end AlgebraicGeometry.AlgebraicStack
