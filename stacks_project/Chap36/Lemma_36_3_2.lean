/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Limit.Cohomology
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X : Scheme.{u}}

/- Lemma 36.3.2 (1): if the transition maps on every cohomology sheaf of a sequential inverse
system in `D_QCoh(𝒪_X)` are epimorphisms, then the cohomology sheaf of a derived limit is
isomorphic to the inverse limit of the cohomology sheaves. -/
@[stacks 0A0J] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.cohomologySheaf_iso_limit_of_epi :
    ∀ (Ksys : SequentialInverseSystem (DerivedQCoh X))
      (K : RingedSpace.ModuleDerived X.toRingedSpace)
      (hK : IsDerivedLimit (Ksys ⋙ inclusion X) K)
      (h_epi : ∀ (q : ℤ) (n : ℕ), Epi
        (SequentialInverseSystem.transitionMap
          (Ksys ⋙ inclusion X ⋙
            DerivedCategory.homologyFunctor X.toRingedSpace.Modules q)
          (Nat.le_succ n)))
      (q : ℤ),
      IsIsomorphic (RingedSpace.ModuleDerived.cohomologySheaf K q)
        (limit (Ksys ⋙ inclusion X ⋙
          DerivedCategory.homologyFunctor X.toRingedSpace.Modules q)))

/- Lemma 36.3.2 (2): under the same degreewise epimorphism hypothesis, the ordinary inverse
limit of the degree-`q` cohomology sheaves, placed in degree zero, is a homotopy limit of their
sequential inverse system. -/
@[stacks 0A0J] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.cohomologySheaf_limit_isOf_of_epi :
    ∀ (Ksys : SequentialInverseSystem (DerivedQCoh X))
      (K : RingedSpace.ModuleDerived X.toRingedSpace)
      (hK : IsDerivedLimit (Ksys ⋙ inclusion X) K)
      (h_epi : ∀ (q : ℤ) (n : ℕ), Epi
        (SequentialInverseSystem.transitionMap
          (Ksys ⋙ inclusion X ⋙
            DerivedCategory.homologyFunctor X.toRingedSpace.Modules q)
          (Nat.le_succ n)))
      (q : ℤ),
      HomotopyLimit.IsOf
        ((Ksys ⋙ inclusion X ⋙
            DerivedCategory.homologyFunctor X.toRingedSpace.Modules q) ⋙
          DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ))
        ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
          (limit (Ksys ⋙ inclusion X ⋙
            DerivedCategory.homologyFunctor X.toRingedSpace.Modules q))))

/- Lemma 36.3.2 (3): under the same hypotheses, the inverse limit of the degree-`q` cohomology
sheaves has vanishing positive cohomology on every affine open. -/
@[stacks 0A0J] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.cohomologySheaf_limit_higherCohomology_isZero_of_epi :
    ∀ (Ksys : SequentialInverseSystem (DerivedQCoh X))
      (K : RingedSpace.ModuleDerived X.toRingedSpace)
      (hK : IsDerivedLimit (Ksys ⋙ inclusion X) K)
      (h_epi : ∀ (q : ℤ) (n : ℕ), Epi
        (SequentialInverseSystem.transitionMap
          (Ksys ⋙ inclusion X ⋙
            DerivedCategory.homologyFunctor X.toRingedSpace.Modules q)
          (Nat.le_succ n)))
      (q : ℤ) (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p),
      IsZero
        (((SheafOfModules.toSheaf X.toRingedSpace.ringCatSheaf).obj
          (limit (Ksys ⋙ inclusion X ⋙
            DerivedCategory.homologyFunctor X.toRingedSpace.Modules q))).H' p U))

end AlgebraicGeometry.Scheme.DerivedQCoh

end
