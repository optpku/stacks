module

import StacksCheckRecall
public import stacks_project.Chap48.Example_48_22_1
public import stacks_project.Chap48.Lemma_48_22_3
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingModule

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ExceptionalInverseImage

/- Lemma 48.22.4 (1) -/
@[stacks 0AWN] #check (AlgebraicGeometry.Scheme.ExceptionalInverseImage.nonzeroCohomology_degreeBounds :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA)
      (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
      (hωS : IsIsomorphic ωS ((ModuleDerived.InternalHom.affineTildeDerived A).obj ωA))
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (fShriek : ExceptionalInverseImage f)
      (d : ℕ) (h_dimension : topologicalKrullDim X = d) (i : ℤ)
      (hi : ¬ IsZero (RingedSpace.ModuleDerived.cohomologySheaf
        (fShriek.functor.obj ωS) i)),
      -(d : ℤ) ≤ i ∧ i ≤ 0)

/- Lemma 48.22.4 (2) -/
@[stacks 0AWN] #check (AlgebraicGeometry.Scheme.ExceptionalInverseImage.cohomology_supportDimension_le :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA)
      (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
      (hωS : IsIsomorphic ωS ((ModuleDerived.InternalHom.affineTildeDerived A).obj ωA))
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (fShriek : ExceptionalInverseImage f)
      (d : ℕ) (h_dimension : topologicalKrullDim X = d) (i : ℤ),
      topologicalKrullDim
          (RingedSpace.moduleSupport (RingedSpace.ModuleDerived.cohomologySheaf
            (fShriek.functor.obj ωS) i)) ≤
        if i ≤ 0 then ((-i).toNat : WithBot ℕ∞) else ⊥)

/- Lemma 48.22.4 (3) -/
@[stacks 0AWN] #check (AlgebraicGeometry.Scheme.ExceptionalInverseImage.dualizingModule_support_eq_topComponents :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA)
      (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
      (hωS : IsIsomorphic ωS ((ModuleDerived.InternalHom.affineTildeDerived A).obj ωA))
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (fShriek : ExceptionalInverseImage f)
      (d : ℕ) (h_dimension : topologicalKrullDim X = d),
      RingedSpace.moduleSupport (RingedSpace.ModuleDerived.cohomologySheaf
          (fShriek.functor.obj ωS) (-(d : ℤ))) =
        ⋃ Z : irreducibleComponents X,
          ⋃ (_ : topologicalKrullDim Z = topologicalKrullDim X), (Z : Set X))

/- Lemma 48.22.4 (4) -/
@[stacks 0AWN] #check (AlgebraicGeometry.Scheme.ExceptionalInverseImage.dualizingModule_satisfiesSerreConditionSTwo :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA)
      (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
      (hωS : IsIsomorphic ωS ((ModuleDerived.InternalHom.affineTildeDerived A).obj ωA))
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (fShriek : ExceptionalInverseImage f)
      (d : ℕ) (h_dimension : topologicalKrullDim X = d),
      @Scheme.Modules.satisfiesSerreConditionS X
        (LocallyOfFiniteType.isLocallyNoetherian f)
        (RingedSpace.ModuleDerived.cohomologySheaf
          (fShriek.functor.obj ωS) (-(d : ℤ)))
        (AlgebraicGeometry.Scheme.isDualizingModule_of_proper
          HA HX ωA hωA ωS hωS f fShriek d h_dimension).coherent 2)

end AlgebraicGeometry.Scheme.ExceptionalInverseImage
