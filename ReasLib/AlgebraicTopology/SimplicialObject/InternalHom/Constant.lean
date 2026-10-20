/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Finiteness
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Constant.Restriction
public import ReasLib.AlgebraicTopology.SimplicialSet.Dimension
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
@stack 017J

# Representability of constant-object restrictions

Degreewise finite sources with the required constant copowers admit representability criteria
under either countable limits or a finite dimension bound and finite limits. The usual nonempty
finite source in a category with binary coproducts supplies these copowers through
`HasCopowers.ofFiniteNonempty`. The restriction itself and its computation API live in
`InternalHom.Constant.Restriction`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject.internalHom

variable {C : Type uC} [Category.{vC} C]

section Finiteness

variable (U : SSet.{uS}) [U.ObjFinite] [HasConstCopowers U C]
variable (T : SimplicialObject C)

namespace constRestriction

/-- A degreewise finite source with constant copowers has representable constant-object mapping
restriction when `C` has countable limits. -/
@[stacks 017J]
theorem isRepresentable.ofCountableLimits [HasCountableLimits C] :
    (constRestriction U T).IsRepresentable := sorry

/-- A degreewise finite, eventually degenerate source with constant copowers has representable
constant-object mapping restriction when `C` has finite limits. -/
@[stacks 017K]
theorem isRepresentable.ofEventuallyDegenerate [HasFiniteLimits C]
    [hU : U.EventuallyDegenerate] :
    (constRestriction U T).IsRepresentable := sorry

end constRestriction

end Finiteness

end CategoryTheory.SimplicialObject.internalHom
