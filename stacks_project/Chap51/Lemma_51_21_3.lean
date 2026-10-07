module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Cohomology.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Scheme.Modules

noncomputable section

universe u

/- Lemma 51.21.3: derived global sections of the twisted derived pullback of any module
on a Noetherian affine blowup are its derived tensor product with the ideal power,
above a cutoff identifying twist cohomology with ideal powers. -/
@[stacks 0G9Z] #check (AlgebraicGeometry.IsBlowup.derivedGlobalSectionsTwistedPullback :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    (q₀ : ℕ)
    (hVanishing : ∀ {r i : ℕ}, q₀ ≤ r → 0 < i →
      IsZero (Scheme.Hom.cohomology p (IsBlowup.twistingSheaf I p (r : ℤ)) i))
    (hSections : ∀ {r : ℕ}, q₀ ≤ r →
      IsIsomorphic (Scheme.Hom.cohomology p (IsBlowup.twistingSheaf I p (r : ℤ)) 0)
        (ModuleCat.of A (I ^ r : Ideal A)))
    (q : ℕ) (hq : q₀ ≤ q) (M : ModuleCat A),
    IsIsomorphic
      ((affineBaseModuleDerivedGlobalSectionsFunctor A p).obj
        (DerivedCategory.DerivedTensor.Right.obj (C := RingedSpace.Modules X.toRingedSpace)
          ((affineBaseModuleDerivedAssociatedFunctor A p).obj
            ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M))
          ((DerivedCategory.singleFunctor X.Modules 0).obj
            (IsBlowup.twistingSheaf I p (q : ℤ)))))
      (DerivedCategory.DerivedTensor.Right.obj
        ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj M)
        ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
          (ModuleCat.of A (I ^ q : Ideal A)))))
