/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ResidueField.Coproduct

/-!
# Generic-point residue-field coproducts

This module defines the coproduct of the spectra of the residue fields at the
generic points of a scheme, together with its canonical morphism to the scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The coproduct of the spectra of the residue fields of the generic points of `X`. -/
noncomputable def genericPointSpectrumCoproduct (X : Scheme.{u}) : Scheme.{u} :=
  pointSpectrumCoproduct X (genericPoints X)

/-- The canonical morphism from the generic-point residue-field coproduct to `X`. -/
noncomputable def genericPointSpectrumCoproductTo (X : Scheme.{u}) :
    genericPointSpectrumCoproduct X ⟶ X :=
  pointSpectrumCoproductTo X (genericPoints X)

/-- The generic-point coproduct map is the coproduct descent map of the residue-field legs. -/
theorem genericPointSpectrumCoproductTo_def (X : Scheme.{u}) :
    genericPointSpectrumCoproductTo X =
      Limits.Sigma.desc (fun η : genericPoints X ↦ X.fromSpecResidueField η.1) := rfl

/-- The `η`-th coproduct leg of `genericPointSpectrumCoproductTo X`. -/
@[simp, reassoc]
theorem genericPointSpectrumCoproductTo_ι (X : Scheme.{u}) (η : genericPoints X) :
    Limits.Sigma.ι
        (fun η : genericPoints X ↦
          Spec (X.residueField η.1)) η ≫
      genericPointSpectrumCoproductTo X =
        X.fromSpecResidueField η.1 := by
  simpa [genericPointSpectrumCoproduct, genericPointSpectrumCoproductTo] using
    pointSpectrumCoproductTo_ι X (genericPoints X) η

end AlgebraicGeometry
