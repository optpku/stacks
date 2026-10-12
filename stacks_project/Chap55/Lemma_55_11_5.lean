/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.MinimalModel

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 55.11.5: In Situation 55.9.3, `X` is a minimal model if and only if the associated
numerical type is minimal. -/
@[stacks 0CA6] #check (AlgebraicGeometry.Scheme.Hom.isMinimalModel_iff_associatedNumericalType_isMinimal :
    (R K : Type u) → [CommRing R] → [IsDomain R] → [IsDiscreteValuationRing R] →
    [Field K] → [Algebra R K] → [IsFractionRing R K] →
    (π : R) → Irreducible π →
    (C : SchemeOverField K) → [Curve C] → [Smooth C.hom] → [Projective C.hom] →
    (h_globalSections : Function.Bijective (globalSectionsMap C.hom)) →
    {X : Scheme.{u}} → (f : X ⟶ Spec (CommRingCat.of R)) →
    [Flat f] → [FiniteType f] → [IsProper f] → [Scheme.Regular X] →
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) →
    (T : NumericalType) →
    T.IsSpecialFiberType R K f
      (regularModel_genericFiberProperties R K C h_globalSections f genericFiberIso) →
    (IsMinimalModel f ↔ T.IsMinimal))

end AlgebraicGeometry.Scheme.Hom
