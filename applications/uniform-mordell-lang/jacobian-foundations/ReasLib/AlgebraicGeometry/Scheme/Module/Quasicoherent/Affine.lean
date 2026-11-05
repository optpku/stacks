module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Coherator

/-!
# Affine Quasicoherent Coherator

This module records the affine identification of the coherator with global sections
followed by the associated quasicoherent module construction.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- On an affine scheme, the coherator is naturally isomorphic to global sections followed by
the associated quasicoherent module functor. -/
theorem affineCoherator_isomorphic (A : CommRingCat.{u}) :
    IsIsomorphic (coherator (Spec A))
      ((AlgebraicGeometry.moduleSpecΓFunctor : (Spec A).Modules ⥤ ModuleCat A) ⋙
        (AlgebraicGeometry.tildeEquiv : ModuleCat A ≌ QCoh (Spec A)).functor) := sorry

end AlgebraicGeometry.Scheme.QCoh
