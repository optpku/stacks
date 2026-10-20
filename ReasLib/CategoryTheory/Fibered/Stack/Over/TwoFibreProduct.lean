/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
public import ReasLib.CategoryTheory.Fibered.Stack.PseudoPullback.Closure
public import ReasLib.CategoryTheory.Fibered.CategoryOver.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Induced
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-fibre products of stacks over a site

The underlying explicit two-fibre-product carrier is owned by
`FiberedCategoryOver.TwoFibreProduct`. This module records the reusable stack-closure theorem at
that ambient layer: the two sources must be stacks, while their common target only needs to be a
prestack. It then specializes this result to a cospan in `StackOver` and lifts the same carrier,
projections, comparison cell, and bilimit cone.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace FiberedCategoryOver.TwoFibreProduct

variable {X Y S :
  FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C}

/-- The fixed-universe specialization of the heterogeneous explicit-pseudo-pullback stack
closure. The common target needs only descent for morphisms. -/
@[stacks 026G "fixed-universe stack closure"]
theorem isStackOnSite
    (F : X ⟶ S) (G : Y ⟶ S)
    [IsStack.OnSite J X.p] [IsStack.OnSite J Y.p]
    [IsPrestack.OnSite J S.p] :
    IsStack.OnSite J (apex F G).p := sorry

end FiberedCategoryOver.TwoFibreProduct

namespace StackOver

namespace TwoFibreProduct

variable {X Y S :
  StackOver.{u, v, max w (max u (max v vB)), max v vB} J}

/-- The underlying fibered category of the two-fibre product of two stack morphisms. -/
@[stacks 026G "stack two-fibre-product ambient owner"]
abbrev ambient
    (F : X ⟶ S) (G : Y ⟶ S) :
    FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C :=
  FiberedCategoryOver.TwoFibreProduct.apex F.hom G.hom

/-- The explicit two-fibre product of stacks is again a stack on the site. This specializes
`FiberedCategoryOver.TwoFibreProduct.isStackOnSite`; the common target supplies more than the
prestack hypothesis needed by the ambient closure theorem. -/
@[stacks 026G "stack two-fibre-product descent owner"]
theorem isStackOnSite
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsStack.OnSite J (ambient F G).p := sorry

/-- The stack-valued two-fibre-product owner, with all non-`Prop` data inherited from
`LocallyInduced.TwoFibreProduct.apex`. -/
@[stacks 026G "stack two-fibre-product apex"]
noncomputable abbrev apex
    (F : X ⟶ S) (G : Y ⟶ S) : StackOver J :=
  StackOver.mk (ambient F G) (isStackOnSite F G)

/-- Forgetting the stack condition from the apex recovers the ambient two-fibre-product
carrier. -/
@[simp, stacks 026G]
theorem apex.toFiberedCategoryOver (F : X ⟶ S) (G : Y ⟶ S) :
    (apex F G).toFiberedCategoryOver = ambient F G := sorry

/-- The left projection from the stack-valued two-fibre product. -/
@[stacks 026G "stack two-fibre-product first projection"]
noncomputable abbrev fst
    (F : X ⟶ S) (G : Y ⟶ S) :
    apex F G ⟶ X :=
  StackOver.Hom.lift (X := apex F G) (Y := X)
    (FiberedCategoryOver.TwoFibreProduct.fst F.hom G.hom)

/-- The ambient morphism underlying the left stack projection is the selected
fibre-category projection. -/
@[simp, stacks 026G]
theorem fst.toMor (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Hom.toMor (fst F G) =
      FiberedCategoryOver.TwoFibreProduct.fst F.hom G.hom := sorry

/-- The right projection from the stack-valued two-fibre product. -/
@[stacks 026G "stack two-fibre-product second projection"]
noncomputable abbrev snd
    (F : X ⟶ S) (G : Y ⟶ S) :
    apex F G ⟶ Y :=
  StackOver.Hom.lift (X := apex F G) (Y := Y)
    (FiberedCategoryOver.TwoFibreProduct.snd F.hom G.hom)

/-- The ambient morphism underlying the right stack projection is the selected
fibre-category projection. -/
@[simp, stacks 026G]
theorem snd.toMor (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Hom.toMor (snd F G) =
      FiberedCategoryOver.TwoFibreProduct.snd F.hom G.hom := sorry

/-- The canonical comparison isomorphism between the two stack-valued projection composites. -/
@[stacks 026G "stack two-fibre-product comparison"]
noncomputable abbrev comparisonIso
    (F : X ⟶ S) (G : Y ⟶ S) :
    fst F G ≫ F ≅ snd F G ≫ G :=
  Bicategory.InducedBicategory.isoMk
    (FiberedCategoryOver.TwoFibreProduct.comparisonIso F.hom G.hom)

/-- Forgetting the full-subbicategory structure from the comparison isomorphism recovers the
ambient two-fibre-product comparison isomorphism. -/
@[simp, stacks 026G]
theorem comparisonIso.toMorIso (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Hom.toMorIso (comparisonIso F G) =
      FiberedCategoryOver.TwoFibreProduct.comparisonIso F.hom G.hom := sorry

/-- The canonical pseudo-pullback cone of stacks over `J`. -/
@[stacks 026G "stack two-fibre-product cone"]
noncomputable abbrev cone
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.PseudoPullbackCone F G :=
  Bicategory.PseudoPullbackCone.inFull
    (IsStack.OnSite.objectProperty J)
    (FiberedCategoryOver.TwoFibreProduct.cone F.hom G.hom)
    (isStackOnSite F G)

/-- The apex of the stack-valued cone is the explicit two-fibre product of stacks. -/
@[simp, stacks 026G]
theorem cone.pt (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).pt = apex F G := sorry

/-- The first leg of the stack-valued cone is its first projection. -/
@[simp, stacks 026G]
theorem cone.fst (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).fst = fst F G := sorry

/-- The second leg of the stack-valued cone is its second projection. -/
@[simp, stacks 026G]
theorem cone.snd (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).snd = snd F G := sorry

/-- The structural cell of the stack-valued cone is its canonical comparison isomorphism. -/
@[simp, stacks 026G]
theorem cone.iso (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).iso = comparisonIso F G := sorry

/-- The canonical stack-valued pseudo-pullback cone satisfies the bilimit universal property. -/
@[stacks 026G "standard pseudo-pullback description"]
instance cone.isBilimit (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).IsBilimit := sorry

section BilimitCheck

variable (F : X ⟶ S) (G : Y ⟶ S)

end BilimitCheck

/- The carrier, projections, comparison, and cone are inherited from the explicit ambient
two-fibre-product construction. The reported `sorryAx` is confined to stack closure and bilimit
proofs. -/

end TwoFibreProduct

/-- The bicategory of stacks over a site has pseudopullbacks. -/
@[stacks 026G "two-fibre products of stacks"]
instance hasPseudoPullbacks :
    Bicategory.HasPseudoPullbacks
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J) := sorry

end StackOver

end CategoryTheory
