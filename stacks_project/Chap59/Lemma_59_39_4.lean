/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 59.39.4: if `f : X ⟶ S` is submersive and the geometric fibres of `f` are
connected, then for every sheaf `F` on `S_étale` one has
`Γ(S, F) = Γ(X, f_small⁻¹ F)`, as bijectivity of `restrictGlobalSection`. -/
@[stacks 0EZK] #check
  (AlgebraicGeometry.Scheme.Etale.restrictGlobalSection_bijective_of_submersive_geometricallyConnected :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Submersive f]
      (h_geomConnected : ∀ y : S, GeometricallyConnected (f.fiberToSpecResidueField y))
      [HasWeakSheafify S.smallEtaleTopology (Type (u + 1))]
      [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
      [∀ P : S.Etaleᵒᵖ ⥤ Type (u + 1),
        (smallEtalePullback f).op.HasLeftKanExtension P]
      (F : Sheaf S.smallEtaleTopology (Type (u + 1))),
      Function.Bijective (restrictGlobalSection f F))
