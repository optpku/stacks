/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Stability
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Arbitrary base change preserves closed, open, and locally closed immersions,
quasi-compactness, universal closedness, separation, quasi-separation, monomorphisms,
surjectivity, universal injectivity, affine and quasi-affine morphisms, local and global
finite type, local and global quasi-finiteness, local and global finite presentation,
relative dimension, universal openness, flatness, syntomic and smooth morphisms,
unramified and G-unramified morphisms, étale and proper morphisms, H-projective,
projective, and locally projective morphisms, finite and integral morphisms,
finite local freeness, universal submersiveness, and universal homeomorphisms. -/
theorem baseChange_properties {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) :
    (IsClosedImmersion f → IsClosedImmersion (pullback.snd f g)) ∧
    (IsOpenImmersion f → IsOpenImmersion (pullback.snd f g)) ∧
    (IsImmersion f → IsImmersion (pullback.snd f g)) ∧
    (QuasiCompact f → QuasiCompact (pullback.snd f g)) ∧
    (UniversallyClosed f → UniversallyClosed (pullback.snd f g)) ∧
    (IsSeparated f → IsSeparated (pullback.snd f g)) ∧
    (QuasiSeparated f → QuasiSeparated (pullback.snd f g)) ∧
    (Mono f → Mono (pullback.snd f g)) ∧
    (Surjective f → Surjective (pullback.snd f g)) ∧
    (UniversallyInjective f → UniversallyInjective (pullback.snd f g)) ∧
    (IsAffineHom f → IsAffineHom (pullback.snd f g)) ∧
    (QuasiAffineHom f → QuasiAffineHom (pullback.snd f g)) ∧
    (LocallyOfFiniteType f → LocallyOfFiniteType (pullback.snd f g)) ∧
    (Scheme.Hom.FiniteType f → Scheme.Hom.FiniteType (pullback.snd f g)) ∧
    (LocallyOfFiniteType f ∧ LocallyQuasiFinite f →
      LocallyOfFiniteType (pullback.snd f g) ∧ LocallyQuasiFinite (pullback.snd f g)) ∧
    (Scheme.Hom.QuasiFinite f → Scheme.Hom.QuasiFinite (pullback.snd f g)) ∧
    (LocallyOfFinitePresentation f → LocallyOfFinitePresentation (pullback.snd f g)) ∧
    (Scheme.Hom.FinitePresentation f → Scheme.Hom.FinitePresentation (pullback.snd f g)) ∧
    (∀ d : ℕ, Scheme.Hom.RelativeDimension f d →
      Scheme.Hom.RelativeDimension (pullback.snd f g) d) ∧
    (UniversallyOpen f → UniversallyOpen (pullback.snd f g)) ∧
    (Flat f → Flat (pullback.snd f g)) ∧
    (Syntomic f → Syntomic (pullback.snd f g)) ∧
    (Smooth f → Smooth (pullback.snd f g)) ∧
    (Unramified f → Unramified (pullback.snd f g)) ∧
    (GUnramified f → GUnramified (pullback.snd f g)) ∧
    (Etale f → Etale (pullback.snd f g)) ∧
    (IsProper f → IsProper (pullback.snd f g)) ∧
    (HProjective f → HProjective (pullback.snd f g)) ∧
    (Projective f → Projective (pullback.snd f g)) ∧
    (LocallyProjective f → LocallyProjective (pullback.snd f g)) ∧
    (IsFinite f → IsFinite (pullback.snd f g)) ∧
    (IsIntegralHom f → IsIntegralHom (pullback.snd f g)) ∧
    (IsFiniteLocallyFree f → IsFiniteLocallyFree (pullback.snd f g)) ∧
    (UniversallySubmersive f → UniversallySubmersive (pullback.snd f g)) ∧
    (UniversalHomeomorphism f → UniversalHomeomorphism (pullback.snd f g)) := sorry

end AlgebraicGeometry.Scheme.Hom
