module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition

/-! # Composition and equality transport of derived étale restriction -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {U X : AlgebraicSpace S}

open CategoryTheory.Functor
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing (restrictFunctorComp)

variable (j : U ⟶ X) [Etale j]

/-- Derived restriction along an étale composite is the composite of the derived
restrictions. -/
def restrictFunctorDerivedCompIso {W : AlgebraicSpace S} (p : W ⟶ U) [Etale p] :
    restrictFunctorDerived j ⋙ restrictFunctorDerived p ≅
      restrictFunctorDerived (p ≫ j) :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
      (ExactFunctor.of (restrictFunctor j)) (ExactFunctor.of (restrictFunctor p))).symm ≪≫
    ExactFunctor.MapDerivedCategory.mapIso
      ((exactFunctor X.Modules W.Modules).isoMk (Iso.refl _)) ≪≫
    Functor.MapDerivedCategory.functorIso (restrictFunctorComp p j)

/-- Transport derived restriction along an equality of étale morphisms. -/
def restrictFunctorDerived_eqToIso {W : AlgebraicSpace S} {p q : W ⟶ X}
    [Etale p] [Etale q] (h : p = q) :
    restrictFunctorDerived p ≅ restrictFunctorDerived q :=
  h ▸ Iso.refl (restrictFunctorDerived p)

end AlgebraicGeometry.AlgebraicSpace.Modules
