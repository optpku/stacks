/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

/-!
# Operations on quasi-finite scheme morphisms

The basic owner is split from its composition and base-change closure API so users can import the
smallest layer matching their argument.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- Quasi-finiteness at a point is preserved and reflected by base change for a locally
finite-type scheme morphism. -/
theorem quasiFiniteAt_iff_of_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f]
    (x' : (pullback f g : Scheme)) :
    (pullback.snd f g).QuasiFiniteAt x' ↔
      f.QuasiFiniteAt ((pullback.fst f g) x') := sorry

/-- The quasi-finite locus commutes with base change for a locally finite-type morphism. -/
@[stacks 01TM]
theorem quasiFiniteAt_locus_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [LocallyOfFiniteType f] :
    {x' : (pullback f g : Scheme) | (pullback.snd f g).QuasiFiniteAt x'} =
      (pullback.fst f g) ⁻¹' {x : X | f.QuasiFiniteAt x} := sorry

/-- Quasi-finite scheme morphisms form a morphism property stable under composition. -/
instance quasiFinite_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @QuasiFinite := sorry

/-- The composite of two quasi-finite morphisms is quasi-finite. -/
@[stacks 01TL]
theorem QuasiFinite.comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : QuasiFinite f) (hg : QuasiFinite g) :
    QuasiFinite (f ≫ g) := sorry

/-- Typeclass form of composition stability for quasi-finite morphisms. -/
@[stacks 01TL]
instance quasiFinite_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiFinite f] [QuasiFinite g] :
    QuasiFinite (f ≫ g) := sorry

/-- Quasi-finite scheme morphisms form a morphism property stable under base change. -/
instance quasiFinite_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @QuasiFinite := sorry

/-- Every base change of a quasi-finite morphism is quasi-finite. -/
@[stacks 01TM]
theorem QuasiFinite.pullback_snd
    {X S S' : Scheme.{u}} {f : X ⟶ S}
    (hf : QuasiFinite f) (g : S' ⟶ S) :
    QuasiFinite (pullback.snd f g) := sorry

/-- Typeclass form of base-change stability for quasi-finite morphisms. -/
@[stacks 01TM]
instance quasiFinite_pullback_snd
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [QuasiFinite f] :
    QuasiFinite (pullback.snd f g) := sorry

end Scheme.Hom
end AlgebraicGeometry
