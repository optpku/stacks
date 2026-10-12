/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Model.ExactSequence

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 55.9.5: the exact sequence and its two displayed map descriptions. -/
@[stacks 0C63] #check
  (AlgebraicGeometry.Scheme.Hom.picardSequence_exact :
    ∀ {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (π : R) (hπ : Irreducible π)
      (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
      [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))),
      (picardSequence C f genericFiberIso n components).Exact)

/- Lemma 55.9.5 (first-map computation) -/
@[stacks 0C63]
#check
  (AlgebraicGeometry.Scheme.Hom.picardSequence_firstMap_one :
    ∀ {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (π : R) (hπ : Irreducible π)
      (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
      [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))),
      firstMap f n components 1 =
        (fun i ↦ (f.specialFiberMultiplicities (components i) : ℤ)))

/- Lemma 55.9.5 (component-map computation) -/
@[stacks 0C63]
#check
  (AlgebraicGeometry.Scheme.Hom.picardSequence_componentMap_basis :
    ∀ {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (π : R) (hπ : Irreducible π)
      (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
      [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
      (i : Fin n),
      componentPicardMap f n components (Pi.single i 1) =
        Scheme.Modules.picardClass
          (f.specialFiberComponent (components i)).associatedSheaf)

end AlgebraicGeometry.Scheme.Hom
