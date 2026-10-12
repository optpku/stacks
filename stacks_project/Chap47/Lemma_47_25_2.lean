/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.RelativeDualizing

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.ModuleCat
open CategoryTheory.ModuleCat.UpperShriek
open DerivedCategory.TStructure
open scoped TensorProduct

noncomputable section

universe u

/- Lemma 47.25.2 -/
@[stacks 0BZW] #check (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizing_boundedFiniteCohomology_of_isPerfect :
  ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A]
    [(algebraMap R A).IsPerfectRingMap]
    (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A)),
    ((t.bounded : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG A))
      (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))))

#check (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizing_hasFiniteTorDimension_of_isPerfect :
  ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A]
    [(algebraMap R A).IsPerfectRingMap]
    (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A)),
    (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))).HasFiniteTorDimensionOver R)

#check (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizing_homothety_isIso_of_isPerfect :
  ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A]
    [(algebraMap R A).IsPerfectRingMap]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
    (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A))
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} A))),
    let ω := p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))
    IsIso (@MonoidalClosed.curry'
      (DerivedCategory (ModuleCat.{u, u} A)) _ _ ω ω (HA.closed ω) (𝟙 ω)))

#check (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizing_boundedFiniteCohomology_of_flat :
  ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A] [Module.Flat R A]
    (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A)),
    ((t.bounded : ObjectProperty (DerivedCategory (ModuleCat.{u, u} A))) ⊓
        DerivedCategory.cohomologyIn (ModuleCat.isFG A))
      (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))))

#check (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizing_hasFiniteTorDimension_of_flat :
  ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A] [Module.Flat R A]
    (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A)),
    (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))).HasFiniteTorDimensionOver R)

#check (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizing_homothety_isIso_of_flat :
  ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A] [Module.Flat R A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
    (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A))
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} A))),
    let ω := p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))
    IsIso (@MonoidalClosed.curry'
      (DerivedCategory (ModuleCat.{u, u} A)) _ _ ω ω (HA.closed ω) (𝟙 ω)))

#check (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizing_isPerfectOver_of_flat :
  ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A] [Module.Flat R A]
    (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A)),
    (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))).IsPerfectOver R)

#check (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizing_baseChange_isDualizing_of_flat :
  ∀ {R A k : Type u} [CommRing R] [CommRing A] [Field k]
    [Algebra R A] [Algebra R k] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra.FiniteType R A] [Module.Flat R A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} (A ⊗[R] k)))]
    (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A))
    (Hk : MonoidalClosed (DerivedCategory (ModuleCat.{u, u} (A ⊗[R] k)))),
    let hNoetherian : IsNoetherianRing (A ⊗[R] k) :=
      Algebra.FiniteType.isNoetherianRing_tensor_left
    @CategoryTheory.DerivedCategory.IsDualizingComplex (A ⊗[R] k) _ hNoetherian _
      ((ModuleCat.derivedExtensionOfScalars
        (algebraMap A (A ⊗[R] k))).obj
          (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R)))) Hk)
