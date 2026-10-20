module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Cotensor
import StacksCheckRecall

/-!
@stack 07KB
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {U V : CosimplicialObject C} {a b : U ⟶ V}
variable [HasFiniteProducts C]
variable (H : Homotopy a b)
variable {m n : SimplexCategory} (f : n ⟶ m)
variable (α : (Δ[1] : SSet.{0}).obj (op m))

/- Equation 14.28.1.1 is the canonical naturality square for degreewise evaluation of a
cosimplicial homotopy. -/
@[stacks 07KB "Equation 14.28.1.1"]
#check (H.naturality f α :
  CommSq (U.map f) (H ((Δ[1] : SSet.{0}).map f.op α)) (H α) (V.map f))

end CategoryTheory.CosimplicialObject
