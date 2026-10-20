/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Model.Torsion

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 55.13.3: In Situation 55.9.3, if `h ≥ 1` is coprime to the gcd of the
special-fibre multiplicities, the `h`-torsion Picard sequence
`0 ⟶ Pic(X)[h] ⟶ Pic(C)[h] ⟶ Pic(T)[h]` is exact. -/
@[stacks 0CAD] #check (AlgebraicGeometry.Scheme.Hom.picardTorsionSequence_exact :
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components)
    (h : ℤ) (h_pos : (1 : ℤ) ≤ h)
    (h_coprime : IsCoprime h (specialFiberMultiplicityGcd f T.n components : ℤ)),
    Function.Injective ((genericFiberPicardRestriction f genericFiberIso).torsionByMap h) ∧
      Function.Exact
        ((genericFiberPicardRestriction f genericFiberIso).torsionByMap h)
        ((picardToNumerical π hπ C h_globalSections f genericFiberIso T components hT).torsionByMap h))

end AlgebraicGeometry.Scheme.Hom
