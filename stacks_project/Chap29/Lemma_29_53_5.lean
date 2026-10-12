/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normalization

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.53.5: for a commutative square of quasi-compact and quasi-separated morphisms of
schemes, there exists a unique morphism between the corresponding relative normalizations making
the induced square of canonical factorizations commute. -/
@[stacks 035J] #check
  (AlgebraicGeometry.Scheme.Hom.existsUnique_map_between_normalizations :
    ∀ {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
      (f₁ : Y₁ ⟶ X₁) [QuasiCompact f₁] [QuasiSeparated f₁]
      (f₂ : Y₂ ⟶ X₂) [QuasiCompact f₂] [QuasiSeparated f₂]
      (gY : Y₂ ⟶ Y₁) (gX : X₂ ⟶ X₁),
      gY ≫ f₁ = f₂ ≫ gX →
      ∃! h : f₂.normalization ⟶ f₁.normalization,
        f₂.toNormalization ≫ h = gY ≫ f₁.toNormalization ∧
          h ≫ f₁.fromNormalization = f₂.fromNormalization ≫ gX)
