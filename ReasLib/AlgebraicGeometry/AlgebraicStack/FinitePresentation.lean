/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Finite presentation morphisms of algebraic stacks

A morphism of algebraic stacks is of finite presentation when it is locally
of finite presentation, quasi-compact, and quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is of finite presentation if it is locally
of finite presentation, quasi-compact, and quasi-separated. -/
@[mk_iff]
class FinitePresentation {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends LocallyOfFinitePresentation f, QuasiCompact f, QuasiSeparated f

namespace FinitePresentation

/-- A finite-presentation morphism of algebraic stacks is locally of finite
presentation, quasi-compact, and quasi-separated. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FinitePresentation f] :
    LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f :=
  sorry

/-- The identity morphism of an algebraic stack is of finite presentation. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    FinitePresentation (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic stacks is of finite presentation. -/
instance of_isIso {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f] :
    FinitePresentation f :=
  sorry

/-- A locally of finite presentation, quasi-compact, and quasi-separated
morphism of algebraic stacks is of finite presentation. -/
instance instOfLocallyOfFinitePresentationQuasiCompactQuasiSeparated
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    FinitePresentation f where
  toLocallyOfFinitePresentation := inferInstance
  toQuasiCompact := inferInstance
  toQuasiSeparated := inferInstance

/-- A finite-presentation morphism of algebraic spaces induces a
finite-presentation 1-morphism of algebraic stacks. -/
instance of_toGroupoids {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.FinitePresentation f] :
    FinitePresentation (AlgebraicSpace.toGroupoids.map f) :=
  sorry

end FinitePresentation

end AlgebraicGeometry.AlgebraicStack
