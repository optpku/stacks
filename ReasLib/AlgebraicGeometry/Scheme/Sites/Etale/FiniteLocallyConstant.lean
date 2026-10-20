/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.YonedaComparison

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A set-valued sheaf on the small étale site of a scheme is finite locally
constant exactly when it is isomorphic to the sheafified representable of an
étale scheme whose structure morphism is finite. -/
theorem finiteLocallyConstant_iff_exists_finiteEtale
    (X : Scheme.{u})
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    Sheaf.IsFiniteLocallyConstant F ↔
      ∃ (U : X.Etale), IsFinite U.hom ∧
        Nonempty (F ≅ X.smallEtaleTopology.sheafifiedRepresentable U) := by
  constructor
  · intro hF
    letI := hF
    exact ⟨FiniteLocallyConstant.representationEtale F,
      FiniteLocallyConstant.representationMap_isFinite F,
      ⟨FiniteLocallyConstant.representationIso F⟩⟩
  · intro hF
    sorry

end AlgebraicGeometry.Scheme
