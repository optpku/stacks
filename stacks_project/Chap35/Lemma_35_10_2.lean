/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Counterexample

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u v w

/- Lemma 35.10.2 (1): the associated-module functor to a big standard site is
fully faithful. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctorFullyFaithful :
    (S : Scheme.{u}) → (τ : StandardTopology) →
      Nonempty (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctor S τ).FullyFaithful)

/- Lemma 35.10.2 (2): the associated-module functor to any of the five small
standard sites is fully faithful. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallModuleFunctorFullyFaithful :
    (S : Scheme.{u}) → (τ : StandardTopology) →
      Nonempty (AlgebraicGeometry.Scheme.AssociatedModule.smallModuleFunctor S τ).FullyFaithful)

/- Lemma 35.10.2 (3): the associated-module functor to a big standard site
preserves colimits of every universe-compatible shape, including direct sums. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctorPreservesColimits :
    (S : Scheme.{u}) → (τ : StandardTopology) → (J : Type v) → [Category.{w} J] →
      PreservesColimitsOfShape J
        (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctor S τ))

/- Lemma 35.10.2 (4): the associated-module functor to any of the five small
standard sites preserves colimits of every universe-compatible shape, including
direct sums. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallModuleFunctorPreservesColimits :
    (S : Scheme.{u}) → (τ : StandardTopology) → (J : Type v) → [Category.{w} J] →
      PreservesColimitsOfShape J
        (AlgebraicGeometry.Scheme.AssociatedModule.smallModuleFunctor S τ))

/- Lemma 35.10.2 (5): the associated-module functor to a big standard site is
right exact. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctorRightExact :
    (S : Scheme.{u}) → (τ : StandardTopology) →
      rightExactFunctor (Scheme.QCoh S)
        (SheafOfModules
          (AlgebraicGeometry.Scheme.AssociatedModule.bigStructureSheaf τ S))
        (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctor S τ))

/- Lemma 35.10.2 (6): the associated-module functor to any of the five small
standard sites is right exact. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallModuleFunctorRightExact :
    (S : Scheme.{u}) → (τ : StandardTopology) →
      rightExactFunctor (Scheme.QCoh S)
        (SheafOfModules
          (AlgebraicGeometry.Scheme.AssociatedModule.StandardSmall.structureSheaf τ S))
        (AlgebraicGeometry.Scheme.AssociatedModule.smallModuleFunctor S τ))

/- Lemma 35.10.2 (7): the associated-module functor to the small étale site is
exact. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallEtaleModuleFunctorExact :
    (S : Scheme.{u}) →
      exactFunctor (Scheme.QCoh S)
        (SheafOfModules
          (AlgebraicGeometry.Scheme.AssociatedModule.StandardSmall.structureSheaf
            .etale S))
        (AlgebraicGeometry.Scheme.AssociatedModule.smallModuleFunctor S .etale))

/- Lemma 35.10.2 (8): on `Spec ℤ`, the associated-module functor to any big
standard site is not exact. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctorNotExact :
    (τ : StandardTopology) →
      ¬ exactFunctor (Scheme.QCoh (Spec (CommRingCat.of ℤ)))
        (SheafOfModules
          (AlgebraicGeometry.Scheme.AssociatedModule.bigStructureSheaf τ
            (Spec (CommRingCat.of ℤ))))
        (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctor
          (Spec (CommRingCat.of ℤ)) τ))

/- Lemma 35.10.2 (9): the canonical tensor comparison for associated modules
on a big standard site is invertible. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigTensorComparisonIsIso :
    (S : Scheme.{u}) → (τ : StandardTopology) → (F G : Scheme.QCoh S) →
      IsIso
        (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleTensorComparison S τ F G))

/- Lemma 35.10.2 (10): the canonical tensor comparison for associated modules
on any of the five small standard sites is invertible. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallTensorComparisonIsIso :
    (S : Scheme.{u}) → (τ : StandardTopology) → (F G : Scheme.QCoh S) →
      IsIso
        (AlgebraicGeometry.Scheme.AssociatedModule.smallModuleTensorComparison S τ F G))

/- Lemma 35.10.2 (11): on a small Zariski or étale site, the internal-Hom
comparison is invertible when its source is finitely presented. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallInternalHomComparisonIsIso :
    (S : Scheme.{u}) → (τ : SmallStandardTopology) → (F G : Scheme.QCoh S) →
      (hF : F.obj.IsFinitePresentation) →
        IsIso (AlgebraicGeometry.Scheme.AssociatedModule.smallModuleInternalHomComparison
          S τ.toStandard F G hF))

/- Lemma 35.10.2 (12): on `Spec ℤ`, the big-site internal-Hom comparison fails
for the finitely presented module `Coker(2 : 𝒪 ⟶ 𝒪)` against the structure
module. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigInternalHomNotPreserved :
    (τ : StandardTopology) →
      ¬ IsIso (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleInternalHomComparison
        (Spec (CommRingCat.of ℤ)) τ
        AlgebraicGeometry.Scheme.AssociatedModule.twoCokernelModule
        (AlgebraicGeometry.Scheme.AssociatedModule.structureModule
          (Spec (CommRingCat.of ℤ)))
        AlgebraicGeometry.Scheme.AssociatedModule.twoCokernelModuleIsFinitePresentation))

/- Lemma 35.10.2 (13): the essential image of the associated-module functor on
a big standard site is closed under extensions. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigEssImageClosedUnderExtensions :
    (S : Scheme.{u}) → (τ : StandardTopology) →
      (AlgebraicGeometry.Scheme.AssociatedModule.bigModuleFunctor S τ).essImage.IsClosedUnderExtensions)

/- Lemma 35.10.2 (14): the essential image of the associated-module functor on
any of the five small standard sites is closed under extensions. -/
@[stacks 06VE] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallEssImageClosedUnderExtensions :
    (S : Scheme.{u}) → (τ : StandardTopology) →
      (AlgebraicGeometry.Scheme.AssociatedModule.smallModuleFunctor S τ).essImage.IsClosedUnderExtensions)
