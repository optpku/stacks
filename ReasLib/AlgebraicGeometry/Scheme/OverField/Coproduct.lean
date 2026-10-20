module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Coproducts of spectra over a field

This file packages the coproduct of spectra of a family of commutative algebras
as a scheme over the base field.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The coproduct of the spectra of a family of commutative `k`-algebras, equipped with
its canonical structure morphism to `Spec k`. -/
noncomputable def sigmaSpec (ι : Type u) (A : ι → CommAlgOverField k) :
    SchemeOverField k :=
  Over.mk (Limits.Sigma.desc fun i : ι ↦
    Spec.map (CommRingCat.ofHom (algebraMap k (A i))))

end AlgebraicGeometry.SchemeOverField
