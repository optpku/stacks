module

public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening

/-!
# Representable flattening functors

This module relates morphisms to a representing object for a flattening functor to flatness
after base change.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Flattening

/-- For a representable flattening functor, a base scheme admits a morphism to the chosen
representing object exactly when the pulled-back module is flat over that base. -/
theorem nonempty_hom_reprX_iff_isFlat {X S : Scheme.{u}} (f : X ⟶ S)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [(functor f ℱ).IsRepresentable] (T : Over S) :
    Nonempty (T ⟶ Functor.reprX (functor f ℱ)) ↔ isFlat f ℱ T := sorry

end AlgebraicGeometry.Scheme.Modules.Flattening
