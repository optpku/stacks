module

public import ReasLib.CategoryTheory.Functor.IndexedCoproduct.HomFamily
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Finiteness
import StacksCheckRecall

/-!
@stack 017D

# Source-facing bridge for Lemma 14.13.2

The reusable compatible-family and corepresentability API is owned by
`CategoryTheory.Functor.indexedCoprod.HomFamily` in
`ReasLib.CategoryTheory.Functor.IndexedCoproduct.HomFamily`.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
variable (U : SSet.{w}) [U.ObjFinite] [U.Nonempty]
variable (V W : SimplicialObject C)

/- Lemma 14.13.2: maps from `U × V` to `W` are naturally identified with compatible
simplex-indexed families of degreewise maps from `V` to `W`. -/
@[stacks 017D]
#check (Functor.indexedCoprod.HomFamily.corepresentableBy U V :
  (Functor.indexedCoprod.HomFamily.functor U V).CorepresentableBy
    (SimplicialObject.copower U V))

/- The underlying pointwise equivalence is available independently of its corepresentability
packaging. -/
#check (Functor.indexedCoprod.HomFamily.homEquiv U V W :
  (SimplicialObject.copower U V ⟶ W) ≃
    Functor.indexedCoprod.HomFamily.Compatible U V W)

end CategoryTheory
