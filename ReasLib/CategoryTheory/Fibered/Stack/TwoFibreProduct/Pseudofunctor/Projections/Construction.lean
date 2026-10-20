module

public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Pseudofunctor.Action
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Pseudofunctor.Projections
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Projection
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.StrongTrans
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection transformations for stack-valued two-fibre products

The ambient transformations combine the neutral projections with the endpoint comparisons for
componentwise cospan forgetting. The public transformations are their canonical full-subbicategory
lifts to stacks.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace StackOver.Groupoids.TwoFibreProduct

variable (J : GrothendieckTopology C)

/-- The ambient first-projection transformation, including the componentwise-forgetful
left-endpoint comparison. -/
@[stacks 02ZL "ambient first projection of stack two-fibre products"]
noncomputable def pseudofunctor.fst.ambient :
    Pseudofunctor.StrongTrans (ambientPseudofunctor J)
      ((Bicategory.Cospan.leftProjection
        (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)).comp
          (StackOver.Groupoids.forget J).toPseudofunctor) :=
  Pseudofunctor.StrongTrans.vcomp
    ((CategoryTheory.TwoFibreProduct.pseudofunctor.fst
      (BasedCategory.isFiberedInGroupoids C)).precomp
        (Bicategory.Cospan.map
          (StackOver.Groupoids.forget J).toPseudofunctor))
    (Bicategory.Cospan.map.leftProjection
      (StackOver.Groupoids.forget J).toPseudofunctor)

/-- The ambient second-projection transformation, including the componentwise-forgetful
right-endpoint comparison. -/
@[stacks 02ZL "ambient second projection of stack two-fibre products"]
noncomputable def pseudofunctor.snd.ambient :
    Pseudofunctor.StrongTrans (ambientPseudofunctor J)
      ((Bicategory.Cospan.rightProjection
        (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)).comp
          (StackOver.Groupoids.forget J).toPseudofunctor) :=
  Pseudofunctor.StrongTrans.vcomp
    ((CategoryTheory.TwoFibreProduct.pseudofunctor.snd
      (BasedCategory.isFiberedInGroupoids C)).precomp
        (Bicategory.Cospan.map
          (StackOver.Groupoids.forget J).toPseudofunctor))
    (Bicategory.Cospan.map.rightProjection
      (StackOver.Groupoids.forget J).toPseudofunctor)

/-- Tag 02ZL: the canonical first projection from the stack-valued two-fibre-product
pseudofunctor to the left endpoint of a bundled cospan. -/
@[stacks 02ZL "first projection of the stack two-fibre-product pseudofunctor"]
noncomputable def pseudofunctor.fst :
    Pseudofunctor.StrongTrans (pseudofunctor J)
      (Bicategory.Cospan.leftProjection
        (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.liftTo
    (ambientPseudofunctor J)
    (Bicategory.Cospan.leftProjection
      (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J))
    (ambientPseudofunctor.isStackOnSite J)
    (pseudofunctor.fst.ambient J)

/-- Tag 02ZL: the canonical second projection from the stack-valued two-fibre-product
pseudofunctor to the right endpoint of a bundled cospan. -/
@[stacks 02ZL "second projection of the stack two-fibre-product pseudofunctor"]
noncomputable def pseudofunctor.snd :
    Pseudofunctor.StrongTrans (pseudofunctor J)
      (Bicategory.Cospan.rightProjection
        (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.liftTo
    (ambientPseudofunctor J)
    (Bicategory.Cospan.rightProjection
      (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J))
    (ambientPseudofunctor.isStackOnSite J)
    (pseudofunctor.snd.ambient J)

end StackOver.Groupoids.TwoFibreProduct

end CategoryTheory
