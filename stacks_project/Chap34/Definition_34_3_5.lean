/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation
import StacksCheckRecall

@[expose] public section

universe u v

#check (CategoryTheory.Pretopology.{v, u} :
  (C : Type u) → [CategoryTheory.Category.{v} C] →
    [CategoryTheory.Limits.HasPullbacks C] → Type (max u v))

#check (AlgebraicGeometry.IsChosenBigSite.{u, v} :
  (P : CategoryTheory.Precoverage AlgebraicGeometry.Scheme.{u}) →
    (carrier : CategoryTheory.Cat.{v, u}) →
    (hasPullbacks : CategoryTheory.Limits.HasPullbacks carrier) →
    (toScheme : CategoryTheory.Functor carrier AlgebraicGeometry.Scheme.{u}) →
    (seedSchemes : Set carrier) →
    (seedCoverings : ∀ X : carrier, Set (CategoryTheory.Presieve X)) →
    (pretopology : @CategoryTheory.Pretopology carrier
      (CategoryTheory.Cat.str carrier) hasPullbacks) → Prop)

#check (AlgebraicGeometry.ChosenBigSite.{u, v} :
  CategoryTheory.Precoverage AlgebraicGeometry.Scheme.{u} →
    Type (max (u + 1) (v + 1)))

#check (AlgebraicGeometry.ChosenBigSite.ofPretopology.{u, v} :
  {P : CategoryTheory.Precoverage AlgebraicGeometry.Scheme.{u}} →
    (carrier : CategoryTheory.Cat.{v, u}) →
    (hasPullbacks : CategoryTheory.Limits.HasPullbacks carrier) →
    (toScheme : CategoryTheory.Functor carrier AlgebraicGeometry.Scheme.{u}) →
    (fullyFaithful : CategoryTheory.Functor.FullyFaithful toScheme) →
    (seedSchemes : Set carrier) →
    (seedCoverings : ∀ X : carrier, Set (CategoryTheory.Presieve X)) →
    (pretopology : @CategoryTheory.Pretopology carrier
      (CategoryTheory.Cat.str carrier) hasPullbacks) →
    (specification : AlgebraicGeometry.IsChosenBigSite P carrier hasPullbacks
      toScheme seedSchemes seedCoverings pretopology) →
    AlgebraicGeometry.ChosenBigSite P)

#check (AlgebraicGeometry.ChosenBigSite.spec.{u, v} :
  {P : CategoryTheory.Precoverage AlgebraicGeometry.Scheme.{u}} →
    (X : AlgebraicGeometry.ChosenBigSite.{u, v} P) →
    AlgebraicGeometry.IsChosenBigSite P X.carrier X.hasPullbacks X.toScheme
      X.seedSchemes X.seedCoverings X.pretopology)

#check (AlgebraicGeometry.ChosenBigSite.toGrothendieck.{u, v} :
  {P : CategoryTheory.Precoverage AlgebraicGeometry.Scheme.{u}} →
    (X : AlgebraicGeometry.ChosenBigSite.{u, v} P) →
    CategoryTheory.GrothendieckTopology X.carrier)

/- Definition 34.3.5: a big Zariski site is a chosen small category of schemes
with selected seed schemes and Zariski coverings, equipped with a pretopology
whose covering families are represented by Zariski covers. -/
@[stacks 020S] #check (AlgebraicGeometry.ChosenBigZariskiSite.{u, v} :
  Type (max (u + 1) (v + 1)))
