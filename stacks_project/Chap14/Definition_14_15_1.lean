module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Functor.IndexedProduct.Functoriality
import StacksCheckRecall

/-!
@stack 0B15
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w v u

variable {C : Type u} [Category.{v} C]
variable (U : CosimplicialObject (Type w)) (V : SimplicialObject C)
variable [HasFiniteProducts C]
variable [U.ObjFinite] [U.ObjNonempty]
variable {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) (u : U.obj (unop n))

/- Definition 14.15.1 (1): the value in degree `n` is the product of copies of `V.obj n`
indexed by the cosimplices `U.obj (unop n)`. -/
@[stacks 0B15 "Definition 14.15.1 (1)"]
#check (Functor.indexedProd U V : SimplicialObject C)

#check (Functor.indexedProd.obj U V n :
  (Functor.indexedProd U V).obj n =
    ∏ᶜ (fun _ : U.obj (unop n) ↦ V.obj n))

/- Definition 14.15.1 (2): a simplicial structure map reindexes by `U.map f.unop` and applies
`V.map f` to every factor. -/
@[stacks 0B15 "Definition 14.15.1 (2)"]
#check (Functor.indexedProd.map U V f :
  (Functor.indexedProd U V).map f =
    Pi.map' (U.map f.unop) (fun _ ↦ V.map f))

#check (Functor.indexedProd.map.π U V f u)
