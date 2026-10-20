/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
import ReasLib.AlgebraicGeometry.Scheme.Regular
import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

section

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)
variable (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
variable (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
variable (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
variable [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
variable (genericFiberIso : C ≅ Over.mk
  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
variable (n : ℕ)
variable (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))

/- The ambient DVR, curve, and model data. -/
#check (inferInstance : IsDiscreteValuationRing R)
#check (inferInstance : IsFractionRing R K)
#check (IsLocalRing.ResidueField R : Type u)
#check (hπ : Irreducible π)
#check (C : SchemeOverField K)
#check (inferInstance : Curve C)
#check (inferInstance : Smooth C.hom)
#check (inferInstance : Projective C.hom)
#check (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
#check (X : Scheme.{u})
#check (f : X ⟶ Spec (CommRingCat.of R))
#check (inferInstance : Flat f)
#check (inferInstance : Scheme.Hom.FiniteType f)
#check (inferInstance : IsProper f)
#check (inferInstance : Scheme.Regular X)
#check (genericFiberIso : C ≅ Over.mk
  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))

/- The special fibre and its explicitly indexed irreducible components. -/
#check (f.fiber (IsLocalRing.closedPoint R) : Scheme.{u})
#check (irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) : Type u)
#check (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
#check (AlgebraicGeometry.Scheme.Hom.specialFiberComponent f :
  irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) → X.IdealSheafData)
#check (AlgebraicGeometry.Scheme.Hom.specialFiberMultiplicities f :
  irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)) →₀ ℕ)

/- Situation 55.9.3 -/
@[stacks 0C61] #check
  (AlgebraicGeometry.Scheme.Hom.specialFiber_eq_weightedSum_of_regularModel f :
    f.specialFiberIdeal =
      AlgebraicGeometry.Scheme.IdealSheafData.effectiveCartierDivisorWeightedSum
        f.specialFiberMultiplicities f.specialFiberComponent)

end
