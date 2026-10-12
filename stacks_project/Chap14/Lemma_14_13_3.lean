/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Projection
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Finiteness
import StacksCheckRecall

@[expose] public section

/-!
@stack 017E

# Lemma 14.13.3

The reusable functoriality and projection API is owned by
`CategoryTheory.SimplicialObject.copower`. The source category of degreewise finite nonempty
simplicial sets is modeled as an `ObjectProperty.FullSubcategory`.
-/

open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]

/- Lemma 14.13.3 (1): copower is functorial simultaneously in a degreewise finite nonempty
simplicial set and in a simplicial object. -/
@[stacks 017E "Lemma 14.13.3 (1)"]
#check (Functor.uncurry.obj (SimplicialObject.copower.ofIndex
    SSet.DegreewiseFiniteNonempty.inclusion) :
  SSet.DegreewiseFiniteNonempty.{w} × SimplicialObject C ⥤ SimplicialObject C)

/- The reusable owner is stored in curried form, following mathlib's bifunctor convention. -/
#check (SimplicialObject.copower.ofIndex SSet.DegreewiseFiniteNonempty.inclusion :
  SSet.DegreewiseFiniteNonempty.{w} ⥤ SimplicialObject C ⥤ SimplicialObject C)

/- With arbitrary small coproducts, the same owner specializes to a bifunctor on all
simplicial sets; this is a stronger library-facing companion, not an extra source assumption. -/
#check @SimplicialObject.copower.bifunctor

/- Lemma 14.13.3 (2): the degreewise fold maps from a copower to its simplicial-object variable
form a natural transformation in both variables. -/
@[stacks 017E "Lemma 14.13.3 (2)"]
#check (Functor.uncurry.map (SimplicialObject.copower.ofIndex.projection
    SSet.DegreewiseFiniteNonempty.inclusion) :
  Functor.uncurry.obj (SimplicialObject.copower.ofIndex
      SSet.DegreewiseFiniteNonempty.inclusion) ⟶
    Functor.uncurry.obj
      ((Functor.const SSet.DegreewiseFiniteNonempty.{w}).obj (𝟭 (SimplicialObject C))))

variable (U : SSet.DegreewiseFiniteNonempty.{w}) (X : SimplicialObject C)
variable (Δ : SimplexCategoryᵒᵖ) (u : U.obj.obj Δ)

/- Degreewise, the canonical projection is the identity after every coproduct injection. -/
#check (SimplicialObject.copower.projection.ι X U.obj Δ u :
  Sigma.ι (fun _ : U.obj.obj Δ ↦ X.obj Δ) u ≫
      (SimplicialObject.copower.projection X U.obj).app Δ =
    𝟙 (X.obj Δ))

end CategoryTheory
