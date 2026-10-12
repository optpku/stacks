/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.Graded.Shift.NatInt
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Module.Shift
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.MultiplicationPresentation
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

/- Lemma 27.10.2: the canonical twist of degree nd is trivial on the basic open defined by a
positive-degree homogeneous element f of degree d. -/
@[stacks 01MS] #check
  (AlgebraicGeometry.Proj.AssociatedModule.Twist.restrictBasicOpen_isTrivial :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (n : ℤ),
      AlgebraicGeometry.RingedSpace.IsTrivial
        ((AlgebraicGeometry.basicOpenRestrict 𝒜 (f : A)).obj
          (AlgebraicGeometry.Proj.AssociatedModule.twistingSheaf 𝒜
            (n * (d : ℤ)))))

/- The same restricted canonical twist is invertible. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.Twist.restrictBasicOpen_invertible :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (n : ℤ),
      MonoidalCategory.isInvertibleObject
        ((AlgebraicGeometry.basicOpenRestrict 𝒜 (f : A)).obj
          (AlgebraicGeometry.Proj.AssociatedModule.twistingSheaf 𝒜
            (n * (d : ℤ)))))

/- Canonical twist multiplication in degrees nd and m becomes an isomorphism on the basic
open. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.TwistMultiplication.restrictBasicOpen_isIso :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      (T : AlgebraicGeometry.Proj.AssociatedModule.TwistMultiplication 𝒜)
      {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (n m : ℤ)
      [MonoidalCategory
        (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)).toScheme.Modules]
      [(AlgebraicGeometry.basicOpenRestrict 𝒜 (f : A)).LaxMonoidal],
      IsIso
        (AlgebraicGeometry.Proj.AssociatedModule.TwistMultiplication.restrictBasicOpenMap
          𝒜 T (f : A)
          (n * (d : ℤ)) m))

/- The action of the degree-nd canonical twist on any twisted module sheaf becomes an
isomorphism on the basic open. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.TwistAction.restrictBasicOpen_isIso :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      [SymmetricCategory (AlgebraicGeometry.Proj 𝒜).Modules]
      (T : AlgebraicGeometry.Proj.AssociatedModule.TwistMultiplication 𝒜)
      (ℱ : (AlgebraicGeometry.Proj 𝒜).Modules)
      {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (n m : ℤ)
      [MonoidalCategory
        (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)).toScheme.Modules]
      [(AlgebraicGeometry.basicOpenRestrict 𝒜 (f : A)).LaxMonoidal],
      IsIso
        (AlgebraicGeometry.Proj.AssociatedModule.TwistAction.restrictBasicOpenMap
          𝒜 T (f : A) ℱ
          (n * (d : ℤ)) m))

/- The canonical comparison from M̃ tensored with the degree-nd twist to the associated sheaf
of the translated grading becomes an isomorphism on the basic open. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison.restrictBasicOpen_isIso :
    ∀ {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]
      (C : AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison 𝒜 ℳ)
      {d : ℕ} (f : 𝒜 d) (hd : 0 < d) (n : ℤ)
      [MonoidalCategory
        (AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)).toScheme.Modules]
      [(AlgebraicGeometry.basicOpenRestrict 𝒜 (f : A)).LaxMonoidal],
      IsIso
        (AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison.restrictBasicOpenMap
          𝒜 ℳ C (f : A) (n * (d : ℤ))))
