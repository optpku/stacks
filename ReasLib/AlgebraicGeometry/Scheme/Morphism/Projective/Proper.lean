/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Properness and descent for projective scheme morphisms

This file collects the properness consequences of local projectivity and the separated
postcomposition descent API for projective morphisms.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- H-projective morphisms are locally projective. -/
theorem HProjective.toLocallyProjective
    {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : HProjective f) :
    LocallyProjective f := sorry

/-- A locally projective morphism is proper. -/
theorem LocallyProjective.isProper
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyProjective f] :
    IsProper f := sorry

/-- Local projectivity supplies the canonical properness structure. -/
instance instIsProperOfLocallyProjective
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyProjective f] :
    IsProper f := sorry

/-- A projective morphism is proper. -/
theorem Projective.isProper
    {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : Projective f) :
    IsProper f := sorry

/-- An H-projective morphism is proper. -/
theorem HProjective.isProper
    {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : HProjective f) :
    IsProper f := sorry

namespace Projective

/-- Projectivity descends across a separated postcomposition. -/
theorem of_comp_of_isSeparated
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    [IsSeparated g] [Projective (f ≫ g)] :
    Projective f := sorry

end Projective

/-- If a composite is projective and its second factor is separated, then its first factor is
projective. -/
@[stacks 0C4Q]
theorem projective_of_comp_of_isSeparated
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    [IsSeparated g] (hfg : Projective (f ≫ g)) :
    Projective f := sorry

end AlgebraicGeometry
