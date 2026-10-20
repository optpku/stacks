module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.Counterexample.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.Counterexample
import StacksCheckRecall

/-!
# A category fibred in groupoids satisfying Artin axioms [0]–[4] but not [5]
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.ArtinVersalityCounterexample
open AlgebraicGeometry.GroupoidsOver
open Functor.Fiber
open scoped AlgebraicGeometry

universe u

/- Example 98.13.2: the annihilator covering condition fails openness of versality. -/
@[stacks 07XR] #check
  (AlgebraicGeometry.ArtinVersalityCounterexample.not_opennessOfVersality :
    ∀ (k : Type u) [Field k],
      ¬ AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
        (AlgebraicGeometry.ArtinVersalityCounterexample.groupoids k))

#check (AlgebraicGeometry.ArtinVersalityCounterexample.exists_qcOpen_iff :
  ∀ {k A : Type u} [Field k] [CommRing A] (φ : coordRing k →+* A),
    HasF φ ↔ ExistsQcOpen φ)

variable (k : Type u) [Field k]

#check (AlgebraicGeometry.ArtinVersalityCounterexample.isCovered_iff k :
  ∀ (T : Over (baseScheme k)),
    IsCovered k T ↔
      ∃ 𝒰 : T.left.AffineOpenCover.{u},
        ∀ j : 𝒰.I₀, HasF (AlgebraicGeometry.Spec.preimage (𝒰.f j ≫ T.hom)).hom)

#check (AlgebraicGeometry.ArtinVersalityCounterexample.groupoids_p k :
  (groupoids k).p = ObjectProperty.ι (IsCovered k))

#check (AlgebraicGeometry.ArtinVersalityCounterexample.instIsStackInGroupoids_etale k :
  IsStack.InGroupoids (Scheme.etaleTopology.over (baseScheme k)) (groupoids k).p)

#check (AlgebraicGeometry.ArtinVersalityCounterexample.instLimitPreserving k :
  AlgebraicGeometry.Groupoids.LimitPreserving (groupoids k))

#check (AlgebraicGeometry.ArtinVersalityCounterexample.instHasRimSchlessinger k :
  AlgebraicGeometry.GroupoidsOver.HasRimSchlessinger (groupoids k))

#check (AlgebraicGeometry.ArtinVersalityCounterexample.finiteDimensional_tangent k :
  ∀ (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k'))),
    FiniteDimensional k' (tangentSpaceAt k k' x0))

#check (AlgebraicGeometry.ArtinVersalityCounterexample.finiteDimensional_infAut k :
  ∀ (k' : Type u) [Field k'] [Algebra (coordRing k) k']
    [Module.Finite (coordRing k) k']
    (x0 : (groupoids k).p.Fiber (Over.mk (fieldToBase k k')))
    (ξ0 : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.residue (coordRing k) k'))
    (ξ0' : (predeformationAt k k' x0).Fiber (ArtinianLocalAlgCat.dualNumber (coordRing k) k'))
    (φ : fiberInclusion.obj ξ0 ⟶ fiberInclusion.obj ξ0')
    [(predeformationAt k k' x0).IsStronglyCocartesian
      (ArtinianLocalAlgCat.residueToDualNumber (coordRing k) k') φ],
    FiniteDimensional k'
      (infinitesimalAutomorphismsAt (predeformationAt k k' x0) ξ0 ξ0' φ))

#check (AlgebraicGeometry.ArtinVersalityCounterexample.instApproximationIsEquivalence k :
  (approximation (groupoids k)).IsEquivalence)

#check (AlgebraicGeometry.ArtinVersalityCounterexample.exists_versal_only_at_origin k :
  IsFiniteTypePoint (origin k) ∧
    IsVersalAt (testToBase k) (identityObject k) (identityObject_over k) (origin k) ∧
      ∀ u : testScheme k, IsFiniteTypePoint u → u ≠ origin k →
        ¬ IsVersalAt (testToBase k) (identityObject k) (identityObject_over k) u)
