/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.GUnramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# G-unramifiedness and local finite presentation

A morphism of algebraic spaces is G-unramified if and only if it is unramified
and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is G-unramified if and only if it is
unramified and locally of finite presentation. -/
theorem gUnramified_iff_unramified_and_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    GUnramified f ↔ Unramified f ∧ LocallyOfFinitePresentation f :=
  sorry

/-- A G-unramified morphism of algebraic spaces is locally of finite
presentation. -/
instance locallyOfFinitePresentation_of_gUnramified {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [GUnramified f] :
    LocallyOfFinitePresentation f :=
  ((gUnramified_iff_unramified_and_locallyOfFinitePresentation f).mp inferInstance).2

/-- An unramified morphism of algebraic spaces that is locally of finite
presentation is G-unramified. -/
instance gUnramified_of_unramified_of_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Unramified f]
    [LocallyOfFinitePresentation f] : GUnramified f :=
  (gUnramified_iff_unramified_and_locallyOfFinitePresentation f).mpr
    ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.AlgebraicSpace
