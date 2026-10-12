/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.TwoFibreProduct.Pseudofunctor.Action
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct.Pseudofunctor.Projections
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Projection
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.StrongTrans
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection transformations for set-stack two-fibre products

The ambient transformations reuse the setoid-stack projections and the endpoint comparisons
for componentwise cospan mapping. Their public lifts retain all naturality and coherence data.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace StackOver.Sets.TwoFibreProduct

variable (J : GrothendieckTopology C)

/-- The ambient first-projection transformation, including the componentwise-forgetful
endpoint comparison. -/
@[stacks 0434 "ambient set-stack first projection transformation"]
noncomputable def pseudofunctor.fst.ambient :
    Pseudofunctor.StrongTrans (ambientPseudofunctor J)
      ((Bicategory.Cospan.leftProjection
        (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)).comp
          (StackOver.Sets.forget J).toPseudofunctor) :=
  Pseudofunctor.StrongTrans.vcomp
    ((StackOver.Setoids.TwoFibreProduct.pseudofunctor.fst J).precomp
      (Bicategory.Cospan.map (StackOver.Sets.forget J).toPseudofunctor))
    (Bicategory.Cospan.map.leftProjection
      (StackOver.Sets.forget J).toPseudofunctor)

/-- The ambient second-projection transformation, including the componentwise-forgetful
endpoint comparison. -/
@[stacks 0434 "ambient set-stack second projection transformation"]
noncomputable def pseudofunctor.snd.ambient :
    Pseudofunctor.StrongTrans (ambientPseudofunctor J)
      ((Bicategory.Cospan.rightProjection
        (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)).comp
          (StackOver.Sets.forget J).toPseudofunctor) :=
  Pseudofunctor.StrongTrans.vcomp
    ((StackOver.Setoids.TwoFibreProduct.pseudofunctor.snd J).precomp
      (Bicategory.Cospan.map (StackOver.Sets.forget J).toPseudofunctor))
    (Bicategory.Cospan.map.rightProjection
      (StackOver.Sets.forget J).toPseudofunctor)

/-- The canonical first projection from the set-stack two-fibre-product pseudofunctor to the
left endpoint of a bundled cospan. -/
@[stacks 0434 "set-stack first projection transformation"]
noncomputable def pseudofunctor.fst :
    Pseudofunctor.StrongTrans (pseudofunctor J)
      (Bicategory.Cospan.leftProjection
        (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.liftTo
    (ambientPseudofunctor J)
    (Bicategory.Cospan.leftProjection
      (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J))
    (ambientPseudofunctor.isFiberedInSets J)
    (pseudofunctor.fst.ambient J)

/-- The canonical second projection from the set-stack two-fibre-product pseudofunctor to the
right endpoint of a bundled cospan. -/
@[stacks 0434 "set-stack second projection transformation"]
noncomputable def pseudofunctor.snd :
    Pseudofunctor.StrongTrans (pseudofunctor J)
      (Bicategory.Cospan.rightProjection
        (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)) :=
  ObjectProperty.FullSubbicategory.StrongTrans.liftTo
    (ambientPseudofunctor J)
    (Bicategory.Cospan.rightProjection
      (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J))
    (ambientPseudofunctor.isFiberedInSets J)
    (pseudofunctor.snd.ambient J)

end StackOver.Sets.TwoFibreProduct

end CategoryTheory
