/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.DerivedBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat

/-!
# Proper flat base change for module cohomology

This file defines derived global sections over an affine base and records perfectness and
arbitrary affine base change for coherent modules that are flat over a proper base morphism.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
variable {X : Scheme.{u}}

/-- For a proper morphism to a Noetherian affine scheme and a coherent module flat over the
base, the canonical derived base-change map is an isomorphism. -/
theorem properFlatCoherent_baseChangeMap_isIso
    [IsNoetherianRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasPair A f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasPair A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseChangeDerivedCompatibility.HasScalarExtension A A']
    [AffineBaseChangeDerivedCompatibility.HasPullback A A' f]
    [AffineBaseChangeDerivedCompatibility.SourceRoute A A' f]
    [AffineBaseChangeDerivedCompatibility.TargetRoute A A' f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (hflat : flatOver ℱ f)
    : IsIso (affineBaseModuleDerivedGlobalSectionsBaseChangeMap A A' f ℱ) := sorry

/-- Derived global sections of a coherent module flat over a proper morphism to a Noetherian
affine scheme form a perfect derived module. -/
theorem properFlatCoherent_affineBaseModuleDerivedGlobalSections_isPerfect
    [IsNoetherianRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (hflat : flatOver ℱ f)
    : (affineBaseModuleDerivedGlobalSections A f ℱ).IsPerfect := sorry

/-- Derived global sections of a coherent module flat over a proper Noetherian affine base are
perfect and commute with arbitrary affine base change. -/
theorem properFlatCoherent_affineBaseModuleDerivedGlobalSections
    [IsNoetherianRing A]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasPair A f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasPair A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseChangeDerivedCompatibility.HasScalarExtension A A']
    [AffineBaseChangeDerivedCompatibility.HasPullback A A' f]
    [AffineBaseChangeDerivedCompatibility.SourceRoute A A' f]
    [AffineBaseChangeDerivedCompatibility.TargetRoute A A' f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (hflat : flatOver ℱ f)
    : (affineBaseModuleDerivedGlobalSections A f ℱ).IsPerfect ∧
      IsIso (affineBaseModuleDerivedGlobalSectionsBaseChangeMap A A' f ℱ) :=
  ⟨properFlatCoherent_affineBaseModuleDerivedGlobalSections_isPerfect
      f ℱ hflat,
    properFlatCoherent_baseChangeMap_isIso
      f ℱ hflat⟩

end AlgebraicGeometry.Scheme.Modules
