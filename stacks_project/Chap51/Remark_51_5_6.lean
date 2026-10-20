module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.ClosedSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Remark 51.5.6 (1): for a Noetherian ring and a specialization-stable subset
`T ⊆ Spec(A)`, bounded-below derived sections `RΓ_T` is right adjoint to the inclusion
`D⁺_T(A) ⥤ D⁺(A)`. -/
@[stacks 0EF4] #check
  (CategoryTheory.ModuleCat.SupportedOn.boundedBelowDerivedSectionsAdjunction :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)],
    (DerivedCategory.Plus.cohomologyIn
        (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))).ι ⊣
      boundedBelowDerivedSections T)

/- Remark 51.5.6 (2): after forgetting the support-valued bounded target,
bounded-below derived sections agree canonically with unbounded derived sections on
`DerivedCategory.Plus.ι.obj K`. -/
@[stacks 0EF4] #check
  (CategoryTheory.ModuleCat.SupportedOn.boundedBelowDerivedSectionsValueIso :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)]
      (K : DerivedCategory.Plus (ModuleCat.{u} A)),
    DerivedCategory.Plus.ι.obj ((boundedBelowDerivedSections T).obj K).obj ≅
      ((ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)).ι.mapDerivedCategory).obj
        ((derivedSections T).obj (DerivedCategory.Plus.ι.obj K)))

/- Remark 51.5.6 (3): if the Noetherian ring `A` has finite Krull dimension, then
unbounded derived sections `RΓ_T` is right adjoint to the inclusion
`D_T(A) ⥤ D(A)`. -/
@[stacks 0EF4] #check
  (CategoryTheory.ModuleCat.SupportedOn.derivedSectionsWithSupportedCohomologyAdjunction :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)]
      [Fact (∃ d : ℕ, Ring.KrullDimLE d A)],
    (DerivedCategory.cohomologyIn
        (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))).ι ⊣
      derivedSectionsWithSupportedCohomology T)

variable (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)]
variable (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ)

/- Remark 51.5.6 (4): `Hⁱ_T(K)` is the degree-`i` cohomology of the total
right-derived supported-sections object `RΓ_T(K)`. -/
@[stacks 0EF4] #check
  (CategoryTheory.ModuleCat.SupportedOn.cohomology_def T K i :
    cohomology T K i =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((derivedInclusion T).obj ((derivedSections T).obj K)))

/- Remark 51.5.6 (5): `derivedSections T` is the total right-derived functor of
the supported-sections functor `coreflector T`. -/
@[stacks 0EF4] #check
  (CategoryTheory.Functor.RightDerived.KInjective.isRightDerived (coreflector T) :
    (derivedSections T).IsRightDerivedFunctor
      (CategoryTheory.Functor.RightDerived.KInjective.unit (coreflector T))
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)))

variable (hT : StableUnderSpecialization T)

/- Remark 51.5.6 (6): `Hⁱ_T(K)` is canonically the filtered colimit of
`Hⁱ_Z(K)` over closed subsets `Z ⊆ T`. -/
@[stacks 0EF4] #check
  (CategoryTheory.ModuleCat.SupportedOn.comparisonIsIso T hT K i :
    IsIso (comparison T hT K i))

end CategoryTheory.ModuleCat.SupportedOn
