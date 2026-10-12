/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.LowDegree
public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer

@[expose] public section

universe v u

namespace CategoryTheory.CosimplicialObject.SplitEqualizer

variable {C : Type u} [Category.{v} C]
variable (S : CosimplicialObject C)

/-- The first coface equalizes the two cofaces out of degree one. -/
theorem condition :
    S.δ (1 : Fin 2) ≫ S.δ (2 : Fin 3) =
      S.δ (1 : Fin 2) ≫ S.δ (1 : Fin 3) := sorry

/-- The degree-zero codegeneracy retracts the source coface. -/
theorem source_retraction :
    S.δ (1 : Fin 2) ≫ S.σ (0 : Fin 1) = 𝟙 _ := sorry

/-- The degree-one codegeneracy retracts the lower parallel coface. -/
theorem bottom_retraction :
    S.δ (1 : Fin 3) ≫ S.σ (0 : Fin 2) = 𝟙 _ := sorry

/-- The upper parallel coface is compatible with the two codegeneracies. -/
theorem top_compatibility :
    S.δ (2 : Fin 3) ≫ S.σ (0 : Fin 2) =
      S.σ (0 : Fin 1) ≫ S.δ (1 : Fin 2) := sorry

/-- The canonical splitting of the first three terms of a cosimplicial object. -/
def splitting : CategoryTheory.IsSplitEqualizer
    (S.δ (2 : Fin 3)) (S.δ (1 : Fin 3)) (S.δ (1 : Fin 2)) where
  leftRetraction := S.σ (0 : Fin 1)
  rightRetraction := S.σ (0 : Fin 2)
  condition := condition S
  ι_leftRetraction := source_retraction S
  bottom_rightRetraction := bottom_retraction S
  top_rightRetraction := top_compatibility S

/-- The equalizer universal property induced by the canonical splitting. -/
def isLimit : Limits.IsLimit (splitting S).asFork :=
  (splitting S).isEqualizer

end CategoryTheory.CosimplicialObject.SplitEqualizer
