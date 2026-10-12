/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Map.Projection
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.StrongTrans
public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoFibreProduct.Pseudofunctor.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ambient projection transformations for stack-valued two-fibre products

The neutral projections are precomposed with componentwise stack forgetting and composed with
the generic endpoint comparisons for `Cospan.map`.
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
/-- The neutral first-projection transformation after precomposition with componentwise stack
forgetting. -/
@[stacks 026G "ambient stack two-fibre-product first projection transformation"]
noncomputable def pseudofunctor.fst.ambient :
    Pseudofunctor.StrongTrans (ambientPseudofunctor J)
      ((Bicategory.Cospan.leftProjection
        (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)).comp
          (StackOver.forget J).toPseudofunctor) :=
  Pseudofunctor.StrongTrans.vcomp
    ((FiberedCategoryOver.TwoFibreProduct.pseudofunctor.fst (C := C)).precomp
      (Bicategory.Cospan.map (StackOver.forget J).toPseudofunctor))
    (Bicategory.Cospan.map.leftProjection
      (StackOver.forget J).toPseudofunctor)

variable (J) in
/-- The neutral second-projection transformation after precomposition with componentwise stack
forgetting. -/
@[stacks 026G "ambient stack two-fibre-product second projection transformation"]
noncomputable def pseudofunctor.snd.ambient :
    Pseudofunctor.StrongTrans (ambientPseudofunctor J)
      ((Bicategory.Cospan.rightProjection
        (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)).comp
          (StackOver.forget J).toPseudofunctor) :=
  Pseudofunctor.StrongTrans.vcomp
    ((FiberedCategoryOver.TwoFibreProduct.pseudofunctor.snd (C := C)).precomp
      (Bicategory.Cospan.map (StackOver.forget J).toPseudofunctor))
    (Bicategory.Cospan.map.rightProjection
      (StackOver.forget J).toPseudofunctor)

end StackOver.TwoFibreProduct

end CategoryTheory
