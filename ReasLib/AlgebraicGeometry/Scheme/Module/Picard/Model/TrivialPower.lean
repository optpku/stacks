module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Model.ExactSequence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Power
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.PrimitiveDivisor

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An invertible module on a regular proper model of a smooth projective curve over a
discrete valuation ring, trivial on the generic fibre and of degree zero on every reduced
special-fibre component, has trivial tensor power indexed by the gcd of the component
multiplicities. -/
theorem gcdTensorPower_trivial
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
        SpecialFiber.componentDegree f (components i)
          (SpecialFiber.instIsProperComponentToResidueField f (components i))
          (SpecialFiber.component_dimension_le_one C h_globalSections f genericFiberIso
            n components i)
          ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj L) = 0) :
    Nonempty
      (RingedSpace.TensorPower.sheaf L (specialFiberMultiplicityGcd f n components) ≅
        (SheafOfModules.unit X.ringCatSheaf : X.Modules)) := sorry

end AlgebraicGeometry.Scheme.Hom
