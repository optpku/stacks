/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoFibreProduct.Pseudofunctor.Projections.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Component comparisons for stack-valued two-fibre-product projections

The generic cospan-map projection comparison introduces an identity tail. These isomorphisms
remove that tail and expose both ambient `2`-cells for direct downstream rewriting.
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

/-- The first-projection component is canonically isomorphic to the lift of the neutral
first-projection component; the isomorphism removes the identity tail introduced by the generic
cospan-map projection comparison. -/
@[stacks 026G "stack two-fibre-product first projection component comparison"]
noncomputable def pseudofunctor.fst.appIso
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor.fst J).app S ≅
      Bicategory.InducedBicategory.mkHom
        ((FiberedCategoryOver.TwoFibreProduct.pseudofunctor.fst
          (C := C)).app
          ((Bicategory.Cospan.map
            (StackOver.forget J).toPseudofunctor).obj S)) :=
  Bicategory.InducedBicategory.isoMk
    (ρ_ ((FiberedCategoryOver.TwoFibreProduct.pseudofunctor.fst
      (C := C)).app
      ((Bicategory.Cospan.map
        (StackOver.forget J).toPseudofunctor).obj S)))

/-- Forgetting the forward first-component comparison gives the forward right-unitor cell. -/
@[simp, stacks 026G "stack two-fibre-product first projection component forward readout"]
theorem pseudofunctor.fst.appIso.hom.toAmbient
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    HEq ((pseudofunctor.fst.appIso S).hom.hom)
      (ρ_ ((FiberedCategoryOver.TwoFibreProduct.pseudofunctor.fst
        (C := C)).app
        ((Bicategory.Cospan.map
          (StackOver.forget J).toPseudofunctor).obj S))).hom := sorry

/-- Forgetting the inverse first-component comparison gives the inverse right-unitor cell. -/
@[simp, stacks 026G "stack two-fibre-product first projection component inverse readout"]
theorem pseudofunctor.fst.appIso.inv.toAmbient
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    HEq ((pseudofunctor.fst.appIso S).inv.hom)
      (ρ_ ((FiberedCategoryOver.TwoFibreProduct.pseudofunctor.fst
        (C := C)).app
        ((Bicategory.Cospan.map
          (StackOver.forget J).toPseudofunctor).obj S))).inv := sorry

/-- The second-projection component is canonically isomorphic to the lift of the neutral
second-projection component; the isomorphism removes the identity tail introduced by the generic
cospan-map projection comparison. -/
@[stacks 026G "stack two-fibre-product second projection component comparison"]
noncomputable def pseudofunctor.snd.appIso
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor.snd J).app S ≅
      Bicategory.InducedBicategory.mkHom
        ((FiberedCategoryOver.TwoFibreProduct.pseudofunctor.snd
          (C := C)).app
          ((Bicategory.Cospan.map
            (StackOver.forget J).toPseudofunctor).obj S)) :=
  Bicategory.InducedBicategory.isoMk
    (ρ_ ((FiberedCategoryOver.TwoFibreProduct.pseudofunctor.snd
      (C := C)).app
      ((Bicategory.Cospan.map
        (StackOver.forget J).toPseudofunctor).obj S)))

/-- Forgetting the forward second-component comparison gives the forward right-unitor cell. -/
@[simp, stacks 026G "stack two-fibre-product second projection component forward readout"]
theorem pseudofunctor.snd.appIso.hom.toAmbient
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    HEq ((pseudofunctor.snd.appIso S).hom.hom)
      (ρ_ ((FiberedCategoryOver.TwoFibreProduct.pseudofunctor.snd
        (C := C)).app
        ((Bicategory.Cospan.map
          (StackOver.forget J).toPseudofunctor).obj S))).hom := sorry

/-- Forgetting the inverse second-component comparison gives the inverse right-unitor cell. -/
@[simp, stacks 026G "stack two-fibre-product second projection component inverse readout"]
theorem pseudofunctor.snd.appIso.inv.toAmbient
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    HEq ((pseudofunctor.snd.appIso S).inv.hom)
      (ρ_ ((FiberedCategoryOver.TwoFibreProduct.pseudofunctor.snd
        (C := C)).app
        ((Bicategory.Cospan.map
          (StackOver.forget J).toPseudofunctor).obj S))).inv := sorry

end StackOver.TwoFibreProduct

end CategoryTheory
