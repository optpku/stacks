module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

@[expose] public section

universe v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The first coface of a cosimplicial object forms a fork over the next two cofaces. -/
def lowDegreeFork (S : CosimplicialObject C) :
    Limits.Fork (S.δ (2 : Fin 3)) (S.δ (1 : Fin 3)) :=
  Limits.Fork.ofι (S.δ (1 : Fin 2)) (S.δ_comp_δ (le_refl (1 : Fin 2)))

end CategoryTheory.CosimplicialObject
