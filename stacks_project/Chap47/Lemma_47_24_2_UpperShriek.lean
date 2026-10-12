/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek

variable {R A : Type u} [CommRing R] [CommRing A]

#check (Presentation : (R →+* A) → Type u)

#check (Presentation.ofSurjection :
  (f : R →+* A) → (n : ℕ) → (g : MvPolynomial (Fin n) R →+* A) →
    g.comp MvPolynomial.C = f → Function.Surjective g → Presentation f)

#check (Presentation.finiteType : ∀ {f : R →+* A}, Presentation f → f.FiniteType)

#check (Presentation.functor : ∀ {f : R →+* A}, Presentation f →
  DerivedCategory (ModuleCat.{u, u} R) ⥤ DerivedCategory (ModuleCat.{u, u} A))

#check (Presentation.functor_obj : ∀ {f : R →+* A} (p : Presentation f)
  (K : DerivedCategory (ModuleCat.{u, u} R)),
  p.functor.obj K =
    (shiftFunctor (DerivedCategory (ModuleCat.{u, u} A)) (p.n : ℤ)).obj
      ((derivedCoextensionOfScalars p.map).obj
        ((derivedExtensionOfScalars
          (MvPolynomial.C : R →+* MvPolynomial (Fin p.n) R)).obj K)))

end CategoryTheory.ModuleCat.UpperShriek
