module

public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The complement projector homotopy

The canonical Dold--Kan complement projector is null-homotopic in every preadditive category.
This construction is independent of kernels, images, and abelian-category homology.

@stack 019C
-/

@[expose] public section

open CategoryTheory AlgebraicTopology HomologicalComplex
open scoped DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace QInfty

/-- The canonical complement projector `Q∞` is explicitly chain-homotopic to zero. -/
@[stacks 019C "null-homotopy of the Dold-Kan complement projector"]
noncomputable def homotopyToZero (U : SimplicialObject C) :
    Homotopy (QInfty : K[U] ⟶ K[U]) 0 :=
  Homotopy.equivSubZero.toFun (homotopyPInftyToId U).symm

end QInfty

end AlgebraicTopology.DoldKan
