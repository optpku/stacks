module

public import Mathlib.RingTheory.FiniteType
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek

variable {R A : Type u} [CommRing R] [CommRing A]

/-- A finite polynomial presentation of a ring homomorphism, recording the chosen polynomial variables, compatible map, and surjectivity data. -/
structure Presentation (f : R →+* A) where
  /-- The number of polynomial variables. -/
  n : ℕ
  /-- The chosen surjection from the polynomial ring to the target. -/
  map : MvPolynomial (Fin n) R →+* A
  /-- The presentation map restricts to the original homomorphism on coefficients. -/
  map_comp : map.comp MvPolynomial.C = f
  /-- The chosen presentation map is surjective. -/
  surjective : Function.Surjective map

namespace Presentation

/-- Construct a polynomial presentation from compatible surjection data. -/
def ofSurjection (f : R →+* A) (n : ℕ) (g : MvPolynomial (Fin n) R →+* A)
    (map_comp : g.comp MvPolynomial.C = f) (surjective : Function.Surjective g) :
    Presentation f :=
  { n := n, map := g, map_comp := map_comp, surjective := surjective }

/-- A finite polynomial presentation implies that the represented ring map is of finite type. -/
theorem finiteType {f : R →+* A} (p : Presentation f) : f.FiniteType := sorry

/-- The upper-shriek functor associated to a chosen finite polynomial presentation, formed by derived extension, derived coextension, and the presentation shift. -/
noncomputable def functor {f : R →+* A} (p : Presentation f) :
    DerivedCategory (ModuleCat.{u, u} R) ⥤ DerivedCategory (ModuleCat.{u, u} A) :=
  derivedExtensionOfScalars
      (MvPolynomial.C : R →+* MvPolynomial (Fin p.n) R) ⋙
    derivedCoextensionOfScalars p.map ⋙
      shiftFunctor (DerivedCategory (ModuleCat.{u, u} A)) (p.n : ℤ)

/-- The objectwise value of the presentation-defined upper-shriek functor. -/
theorem functor_obj {f : R →+* A} (p : Presentation f)
    (K : DerivedCategory (ModuleCat.{u, u} R)) :
    p.functor.obj K =
      (shiftFunctor (DerivedCategory (ModuleCat.{u, u} A)) (p.n : ℤ)).obj
        ((derivedCoextensionOfScalars p.map).obj
          ((derivedExtensionOfScalars
            (MvPolynomial.C : R →+* MvPolynomial (Fin p.n) R)).obj K)) := sorry

end Presentation

end CategoryTheory.ModuleCat.UpperShriek
