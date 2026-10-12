/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import stacks_project.Chap61.Lemma_61_23_1_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.23.1

For a quasi-compact quasi-separated morphism of schemes, pushforward along
`f` commutes with `ε⁻¹` from the small étale site to the small pro-étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProEt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [QuasiCompact f] [QuasiSeparated f]

/-- Lemma 61.23.1 (1): for a quasi-compact quasi-separated morphism `f : X ⟶ Y` and a
sheaf of sets `F` on `X_étale`, the canonical mate
`ε⁻¹ (f_étale,* F) ⟶ f_proétale,* (ε⁻¹ F)` is an isomorphism. -/
@[stacks 09A6]
theorem etaleToProEt_pushforwardHom_isIso
    [∀ F : Y.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt Y).op.HasLeftKanExtension F]
    [∀ F : X.Etaleᵒᵖ ⥤ Type (u + 1), (etaleToProEt X).op.HasLeftKanExtension F]
    [∀ F : Y.Etaleᵒᵖ ⥤ Type (u + 1), (smallEtalePullback f).op.HasLeftKanExtension F]
    [∀ F : Y.ProEtᵒᵖ ⥤ Type (u + 1), (baseChange f).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [HasWeakSheafify (topology X) (Type (u + 1))]
    [HasWeakSheafify (topology Y) (Type (u + 1))]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    IsIso ((etaleToProEt_pushforwardHom (Type (u + 1)) f).app F) :=
  sorry

/-- Lemma 61.23.1 (2): for a quasi-compact quasi-separated morphism `f : X ⟶ Y` and an
abelian sheaf `F` on `X_étale`, the canonical mate
`ε⁻¹ (Rf_étale,* F) ⟶ Rf_proétale,* (ε⁻¹ F)` is an isomorphism. -/
@[stacks 09A6]
theorem etaleToProEt_derivedPushforwardHom_isIso
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify (topology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology Y) AddCommGrpCat.{u + 1}]
    [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt Y).op.HasLeftKanExtension F]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleToProEt X).op.HasLeftKanExtension F]
    [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback f).op.HasLeftKanExtension F]
    [∀ F : Y.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (baseChange f).op.HasLeftKanExtension F]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (etaleToProEt_derivedPushforwardHom f F) :=
  sorry

end AlgebraicGeometry.Scheme
