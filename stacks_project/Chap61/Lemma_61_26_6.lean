/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import stacks_project.Chap61.Definition_61_26_1_ExtensionByZero
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Lemma 61.26.6: if `j : U ⟶ X` is a quasi-compact open immersion of
schemes, then `abelianExtensionByZero j : Ab(U_proétale) ⥤ Ab(X_proétale)`
preserves limits. -/
@[stacks 09BP]
instance abelianExtensionByZero_preservesLimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    [∀ F : U.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) AddCommGrpCat.{u + 1}] :
    PreservesLimits (abelianExtensionByZero j) := sorry

end AlgebraicGeometry.Scheme.ProEt
