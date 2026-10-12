/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.«96_9_4_1_Comparison»

/-!
# Small-étale comparison morphisms of étale modules

The comparison `c_φ` for an étale `𝒪_X`-module is the existing morphism
`moduleComparison`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The comparison morphism
`c_φ : f_small^*(F|_{U'_étale}) ⟶ F|_{U_étale}` of étale `𝒪_X`-modules. -/
abbrev etaleModuleComparison {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (F : etaleModules X) :=
  moduleComparison φ F

/-- `etaleModuleComparison` is the tagged comparison `moduleComparison`. -/
theorem etaleModuleComparison_eq {X : GroupoidsOver S} {x y : X.total}
    (φ : x ⟶ y) (F : etaleModules X) :
    etaleModuleComparison φ F = moduleComparison φ F :=
  sorry

end AlgebraicGeometry.GroupoidsOver
