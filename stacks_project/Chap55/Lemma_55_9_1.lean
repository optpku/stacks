/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
variable (h_globalSections : Function.Bijective (globalSectionsMap C.hom))
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable [Flat f] [FiniteType f] [IsProper f] [Scheme.Regular X]
variable (genericFiberIso : C ≅ Over.mk
  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
variable (i : irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))

/- Lemma 55.9.1 (1): the special fibre of a regular model of a smooth curve over the
fraction field of a discrete valuation ring is an effective Cartier divisor. -/
@[stacks 0C5Z] #check
  (AlgebraicGeometry.Scheme.Hom.instIsEffectiveCartierDivisorSpecialFiber f :
    IsEffectiveCartierDivisor (f.fiberι (IsLocalRing.closedPoint R)))

/- Lemma 55.9.1 (2): every reduced irreducible component of the special fibre of a regular
model is an effective Cartier divisor on the total space. -/
@[stacks 0C5Z] #check
  (AlgebraicGeometry.Scheme.Hom.instIsEffectiveCartierDivisorSpecialFiberComponent
    f i : IsEffectiveCartierDivisor (f.specialFiberComponent i).subschemeι)

/- Lemma 55.9.1 (3): the special fibre is the sum of its reduced irreducible components,
weighted by their multiplicities. -/
@[stacks 0C5Z] #check
  (AlgebraicGeometry.Scheme.Hom.specialFiber_eq_weightedSum_of_regularModel f :
    f.specialFiberIdeal =
      Scheme.IdealSheafData.effectiveCartierDivisorWeightedSum
        f.specialFiberMultiplicities f.specialFiberComponent)

/- Lemma 55.9.1 (4): the invertible sheaf associated to the special fibre of a regular model
is isomorphic to the structure sheaf. -/
@[stacks 0C5Z] #check
  (AlgebraicGeometry.Scheme.Hom.specialFiberAssociatedSheaf_isIsomorphic f :
    IsIsomorphic f.specialFiberIdeal.associatedSheaf
      (SheafOfModules.unit X.ringCatSheaf : X.Modules))

end AlgebraicGeometry.Scheme.Hom
