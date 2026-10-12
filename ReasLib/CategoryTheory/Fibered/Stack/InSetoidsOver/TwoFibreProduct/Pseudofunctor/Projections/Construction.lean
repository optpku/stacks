/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct.Pseudofunctor.Action
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Pseudofunctor.Projections
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Projection
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.StrongTrans
import Mathlib.Tactic.CrossRefAttribute
/-!
# Projection transformations for setoid-stack two-fibre products

The ambient transformations combine the groupoid-stack projections with the endpoint
comparisons for componentwise cospan forgetting. The public transformations are their canonical
full-subbicategory lifts.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace StackOver.Setoids.TwoFibreProduct

variable (J : GrothendieckTopology C)

/-- The ambient first-projection transformation, including the componentwise-forgetful
left-endpoint comparison. -/
@[stacks 0434 "ambient setoid-stack first projection transformation"]
noncomputable def pseudofunctor.fst.ambient :
    Pseudofunctor.StrongTrans (ambientPseudofunctor J)
      ((Bicategory.Cospan.leftProjection
        (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)).comp
          (StackOver.Setoids.forget J).toPseudofunctor) :=
  Pseudofunctor.StrongTrans.vcomp
    ((StackOver.Groupoids.TwoFibreProduct.pseudofunctor.fst J).precomp
      (Bicategory.Cospan.map (StackOver.Setoids.forget J).toPseudofunctor))
    (Bicategory.Cospan.map.leftProjection
      (StackOver.Setoids.forget J).toPseudofunctor)

/-- The ambient second-projection transformation, including the componentwise-forgetful
right-endpoint comparison. -/
@[stacks 0434 "ambient setoid-stack second projection transformation"]
noncomputable def pseudofunctor.snd.ambient :
    Pseudofunctor.StrongTrans (ambientPseudofunctor J)
      ((Bicategory.Cospan.rightProjection
        (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)).comp
          (StackOver.Setoids.forget J).toPseudofunctor) :=
  Pseudofunctor.StrongTrans.vcomp
    ((StackOver.Groupoids.TwoFibreProduct.pseudofunctor.snd J).precomp
      (Bicategory.Cospan.map (StackOver.Setoids.forget J).toPseudofunctor))
    (Bicategory.Cospan.map.rightProjection
      (StackOver.Setoids.forget J).toPseudofunctor)

/-- The canonical first projection from the setoid-stack two-fibre-product pseudofunctor to the
left endpoint of a bundled cospan. -/
@[stacks 0434 "setoid-stack first projection transformation"]
noncomputable def pseudofunctor.fst :
    Pseudofunctor.StrongTrans (pseudofunctor J)
      (Bicategory.Cospan.leftProjection
        (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.liftTo
    (ambientPseudofunctor J)
    (Bicategory.Cospan.leftProjection
      (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J))
    (ambientPseudofunctor.isFiberedInSetoids J)
    (pseudofunctor.fst.ambient J)

/-- The canonical second projection from the setoid-stack two-fibre-product pseudofunctor to the
right endpoint of a bundled cospan. -/
@[stacks 0434 "setoid-stack second projection transformation"]
noncomputable def pseudofunctor.snd :
    Pseudofunctor.StrongTrans (pseudofunctor J)
      (Bicategory.Cospan.rightProjection
        (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.liftTo
    (ambientPseudofunctor J)
    (Bicategory.Cospan.rightProjection
      (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J))
    (ambientPseudofunctor.isFiberedInSetoids J)
    (pseudofunctor.snd.ambient J)

end StackOver.Setoids.TwoFibreProduct

end CategoryTheory
