module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Cotensor.Base
import StacksCheckRecall

/-!
@stack 019V
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe w v u

variable {C : Type u} [Category.{v} C]
variable (U : SSet.{w}) (V : CosimplicialObject C)
variable [HasFiniteProducts C]
variable [U.ObjFinite] [U.Nonempty]
variable {m n : SimplexCategory} (f : m ⟶ n) (u : U.obj (op n))

/- Definition 14.14.1 (1): the value in degree `n` is the product of copies of `V.obj n`
indexed by the simplices `U.obj (op n)`. -/
@[stacks 019V "Definition 14.14.1 (1)"]
#check (CosimplicialObject.cotensor U V : CosimplicialObject C)

#check (CosimplicialObject.cotensor.obj U V n :
  (CosimplicialObject.cotensor U V).obj n =
    ∏ᶜ (fun _ : U.obj (op n) ↦ V.obj n))

/- Definition 14.14.1 (2): a cosimplicial structure map reindexes by `U.map f.op` and applies
`V.map f` to every factor. -/
@[stacks 019V "Definition 14.14.1 (2)"]
#check (CosimplicialObject.cotensor.map U V f :
  (CosimplicialObject.cotensor U V).map f =
    Pi.map' (U.map f.op) (fun _ ↦ V.map f))

#check (CosimplicialObject.cotensor.map.π U V f u)
