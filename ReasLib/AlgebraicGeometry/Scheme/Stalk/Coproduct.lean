/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Coproducts of spectra of scheme stalks

This file defines the coproduct of the spectra of all stalk rings of a scheme
and its canonical comparison morphism to the scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The coproduct, indexed by the points of `X`, of the spectra of the stalk rings of `X`. -/
noncomputable def stalkSpectrumCoproduct (X : Scheme.{u}) : Scheme.{u} :=
  ∐ fun x : X ↦ Spec (X.presheaf.stalk x)

/-- The canonical morphism from the coproduct of the spectra of the stalks of `X` to `X`. -/
noncomputable def stalkSpectrumCoproductTo (X : Scheme.{u}) :
    stalkSpectrumCoproduct X ⟶ X :=
  Limits.Sigma.desc (fun x : X ↦ X.fromSpecStalk x)

/-- The stalk-spectrum coproduct map is the coproduct descent map of the canonical stalk legs. -/
theorem stalkSpectrumCoproductTo_def (X : Scheme.{u}) :
    stalkSpectrumCoproductTo X =
      Limits.Sigma.desc (fun x : X ↦ X.fromSpecStalk x) := rfl

/-- The `x`-th coproduct leg of `stalkSpectrumCoproductTo X` is `X.fromSpecStalk x`. -/
@[simp, reassoc]
theorem stalkSpectrumCoproductTo_ι (X : Scheme.{u}) (x : X) :
    Limits.Sigma.ι
        (fun y : X ↦ Spec (X.presheaf.stalk y)) x ≫
      stalkSpectrumCoproductTo X =
        X.fromSpecStalk x := sorry

end AlgebraicGeometry
