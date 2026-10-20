module

public import ReasLib.RingTheory.Topology.FiniteType.Adic
import StacksCheckRecall

@[expose] public section

open TopologicalRing

universe u

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]

/- Lemma 88.11.1
The eight equivalent finite-type conditions for continuous homomorphisms of
adic rings with finitely generated ideals of definition. -/
@[stacks 0GBW] #check (RingHom.isAdicHom_and_topologicallyOfFiniteType_tfae :
    ∀ {φ : A →+* B} (hφ : Continuous φ),
    List.TFAE
      [φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType,
        φ.IsTaut ∧ φ.TopologicallyOfFiniteType,
        φ.IsAdicHom ∧ φ.IsFiniteTypeOnSomeSpecialFiber,
        φ.IsAdicAndFiniteTypeOnEverySpecialFiber,
        φ.IsAdicAndTopologicallyFiniteTypeOnSome,
        φ.IsAdicAndTopologicallyFiniteTypeOnEvery,
        φ.IsClosedQuotientOfRestrictedPowerSeries,
        φ.IsClosedQuotientOfPolynomialCompletion])

#check (RingHom.TopologicallyOfFiniteType.adic_iff_taut :
    ∀ {φ : A →+* B} (hφ : Continuous φ),
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType)

#check (RingHom.TopologicallyOfFiniteType.adic_iff_restrictedPowerSeries :
    ∀ {φ : A →+* B} (hφ : Continuous φ),
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsClosedQuotientOfRestrictedPowerSeries)

#check (RingHom.TopologicallyOfFiniteType.adic_iff_polynomialCompletion :
    ∀ {φ : A →+* B} (hφ : Continuous φ),
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsClosedQuotientOfPolynomialCompletion)

#check (RingHom.TopologicallyOfFiniteType.adic_iff_completeAlgebra :
    ∀ {φ : A →+* B} (hφ : Continuous φ),
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsAdicAndTopologicallyFiniteTypeOnSome)

#check (TopologicalRing.IsAdicStarRing.isLocalMorphismProperty_isAdicHom_and_topologicallyOfFiniteType :
    TopologicalRing.IsAdicStarRing.IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType)
