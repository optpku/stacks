/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Basis.Algebraic.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v w u1

variable {X : Type u} [TopologicalSpace X]
variable {C : Type v} [Category.{w} C]
variable {B : Set (Opens X)}
variable (F : C ⥤ Type u1) [IsAlgebraicStructure C F]

/-
The functor category and natural transformations are the canonical owners for presheaves and
their morphisms. The source's phrase “type of algebraic structure” is represented by
`IsAlgebraicStructure C F`. The reusable sheaf category is `AlgebraicBasisSheaf F B`; the
source specializes this neutral owner to a topological basis.
-/

/- Definition 6.30.8 (1): a presheaf with values in the fixed type of algebraic structure
`(C, F)` on the basis `B` is a contravariant `C`-valued functor on the category of basis opens. -/
@[stacks 009P "presheaves of algebraic structures on a basis"]
#check ((BasisOpen B)ᵒᵖ ⥤ C)

variable (ℱ 𝒢 : (BasisOpen B)ᵒᵖ ⥤ C)

/- Definition 6.30.8 (2): a morphism of `C`-valued presheaves on `B` is a natural
transformation, expressing compatibility with all restriction maps. -/
@[stacks 009P "morphisms of algebraic-structure-valued basis presheaves"]
#check (ℱ ⟶ 𝒢)

/- Definition 6.30.8 (3): the underlying presheaf of sets of `ℱ` is the composite `ℱ ⋙ F`,
whose value on `U` is `F.obj (ℱ.obj U)`. -/
@[stacks 009P "the underlying set-valued basis presheaf"]
#check (ℱ ⋙ F)

/- Definition 6.30.8 (4): sheaves with values in the type of algebraic structure `(C, F)` on
`B` are the `C`-valued basis presheaves whose underlying presheaves of sets are basis sheaves. -/
@[stacks 009P "sheaves of algebraic structures on a basis"]
#check (AlgebraicBasisSheaf F B)
