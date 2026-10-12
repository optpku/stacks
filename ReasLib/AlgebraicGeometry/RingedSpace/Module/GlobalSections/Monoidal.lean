/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Monoidal

/-!
# Monoidal global sections of module sheaves

Global sections with scalars restricted along a homomorphism into the global-sections ring form
the right adjoint of the strong-monoidal associated-module functor, and therefore carry a
canonical lax-monoidal structure.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- Global sections with scalars restricted along `alpha` are canonically lax monoidal. -/
noncomputable instance moduleGlobalSectionsRestrictionFunctorLaxMonoidal
    {R : Type u} [CommRing R] (X : RingedSpace.{u})
    (alpha : R →+* X.globalSectionsRing) :
    (moduleGlobalSectionsRestrictionFunctor X alpha).LaxMonoidal :=
  (Module.Associated.adjunction alpha).rightAdjointLaxMonoidal

end AlgebraicGeometry.RingedSpace

end
