/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Model.TrivialPower

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 55.13.1: In Situation 55.9.3, an invertible module trivial on the generic
fibre and of degree zero on every indexed special-fibre component has trivial tensor
power indexed by the gcd of the special-fibre multiplicities. -/
@[stacks 0CAB] #check (AlgebraicGeometry.Scheme.Hom.gcdTensorPower_trivial :
  ∀
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
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
    (L : X.Modules) [Scheme.Modules.Invertible L]
    (h_generic_trivial :
      Nonempty
        ((Scheme.Modules.pullback
            (genericFiberIso.hom.left ≫
              pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))))).obj L ≅
          (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules)))
    (h_component_degree :
      ∀ i : Fin n,
        AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentDegree f (components i)
          (AlgebraicGeometry.Scheme.Hom.SpecialFiber.instIsProperComponentToResidueField
            f (components i))
          (AlgebraicGeometry.Scheme.Hom.SpecialFiber.component_dimension_le_one
            C h_globalSections f genericFiberIso n components i)
          ((Scheme.Modules.pullback
            (AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentInclusion f (components i))).obj L) = 0),
    Nonempty
      (RingedSpace.TensorPower.sheaf L
          (AlgebraicGeometry.Scheme.Hom.specialFiberMultiplicityGcd f n components) ≅
        (SheafOfModules.unit X.ringCatSheaf : X.Modules)))
