module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoFibreProduct.Pseudofunctor.Projections.Ambient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection transformations for stack-valued two-fibre products

The ambient transformations lift through the full subbicategory of stacks to the canonical
endpoint projections on bundled cospans of stacks.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.TwoFibreProduct

variable (J) in
/-- The canonical first projection from the stack-valued two-fibre-product pseudofunctor to the
left-endpoint projection on bundled cospans of stacks. -/
@[stacks 026G "stack two-fibre-product first projection transformation"]
noncomputable def pseudofunctor.fst :
    Pseudofunctor.StrongTrans (pseudofunctor J)
      (Bicategory.Cospan.leftProjection
        (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.liftTo
    (ambientPseudofunctor J)
    (Bicategory.Cospan.leftProjection
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J))
    (ambientPseudofunctor.isStackOnSite J) (pseudofunctor.fst.ambient J)

variable (J) in
/-- The canonical second projection from the stack-valued two-fibre-product pseudofunctor to the
right-endpoint projection on bundled cospans of stacks. -/
@[stacks 026G "stack two-fibre-product second projection transformation"]
noncomputable def pseudofunctor.snd :
    Pseudofunctor.StrongTrans (pseudofunctor J)
      (Bicategory.Cospan.rightProjection
        (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.liftTo
    (ambientPseudofunctor J)
    (Bicategory.Cospan.rightProjection
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J))
    (ambientPseudofunctor.isStackOnSite J) (pseudofunctor.snd.ambient J)

end StackOver.TwoFibreProduct

end CategoryTheory
