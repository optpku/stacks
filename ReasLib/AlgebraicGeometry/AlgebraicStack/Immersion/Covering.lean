/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Representable.Covering
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.BaseChange
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Fppf
import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenImmersion.Fpqc
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Fpqc
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc.Comparison

/-!
# Testing immersions of algebraic stacks on an fppf covering

An immersion, open immersion, or closed immersion of algebraic stacks can be
tested after base change along a surjective, flat, locally finitely presented
morphism from an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

private theorem fppfPrecoverage_le_fpqcPrecoverage (S : Scheme.{u}) :
    AlgebraicSpace.fppfPrecoverage S ≤ AlgebraicSpace.fpqcPrecoverage S := by
  intro W R hR
  obtain ⟨𝒰, rfl⟩ := R.exists_eq_preZeroHypercover
  exact (AlgebraicSpace.ofArrows_mem_fpqcPrecoverage_iff 𝒰.f).mpr
    (AlgebraicSpace.fpqcCovering_of_fppfCovering
      ((AlgebraicSpace.fppfCovering_iff_mem_precoverage 𝒰.X 𝒰.f).mpr hR))

local instance openImmersion_isLocalAtTargetFppf {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.IsOpenImmersion S : MorphismProperty (AlgebraicSpace S))
      (AlgebraicSpace.fppfPrecoverage S) :=
  MorphismProperty.IsLocalAtTarget.of_le (fppfPrecoverage_le_fpqcPrecoverage S)

local instance closedImmersion_isLocalAtTargetFppf {S : Scheme.{u}} :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.IsClosedImmersion S : MorphismProperty (AlgebraicSpace S))
      (AlgebraicSpace.fppfPrecoverage S) :=
  MorphismProperty.IsLocalAtTarget.of_le (fppfPrecoverage_le_fpqcPrecoverage S)

private theorem representable_and_has_iff_of_representing
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (P : MorphismProperty (AlgebraicSpace S)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    (relativelyRepresentableByAlgebraicSpaces f ∧ has P f) ↔ P v := by
  have hf : relativelyRepresentableByAlgebraicSpaces f := by
    apply (AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_iff_of_covering f g).mpr
    obtain ⟨eW, eV, h⟩ := hv
    exact ⟨V, ⟨eV⟩⟩
  constructor
  · intro h
    exact (has_iff_of_covering P hf g hv).mp h.2
  · intro h
    exact ⟨hf, (has_iff_of_covering P hf g hv).mpr h⟩

private theorem representable_and_has_iff_exists_covering
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (P : MorphismProperty (AlgebraicSpace S)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    (relativelyRepresentableByAlgebraicSpaces f ∧ has P f) ↔
      ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
        RepresentsTwoFibreProductOnSpace f g V W v ∧ P v := by
  constructor
  · rintro ⟨hf, hP⟩
    obtain ⟨V, ⟨eV⟩⟩ :=
      (AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_iff_of_covering f g).mp hf
    let eW := Bicategory.Equivalence.id W.toGroupoids
    obtain ⟨v, hv, _⟩ :=
      RepresentsTwoFibreProductOnSpace.exists_morphism f g V W eW eV
    have hrep : RepresentsTwoFibreProductOnSpace f g V W v := ⟨eW, eV, hv⟩
    exact ⟨V, v, hrep, (has_iff_of_covering P hf g hrep).mp hP⟩
  · rintro ⟨V, v, hv, hP⟩
    exact (representable_and_has_iff_of_representing P f g hv).mpr hP

namespace OpenImmersion

/-- A morphism of algebraic stacks is an open immersion if and only if
its base change along a surjective, flat, locally finitely presented morphism
from an algebraic space is represented by an open immersion of algebraic
spaces. -/
theorem iff_of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    OpenImmersion f ↔
      ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
        RepresentsTwoFibreProductOnSpace f g V W v ∧
          AlgebraicSpace.IsOpenImmersion v := by
  constructor
  · intro hf
    exact (representable_and_has_iff_exists_covering
      (@AlgebraicSpace.IsOpenImmersion S) f g).mp ⟨hf.representable, hf.of_represents⟩
  · intro h
    obtain ⟨hf, hP⟩ := (representable_and_has_iff_exists_covering
      (@AlgebraicSpace.IsOpenImmersion S) f g).mpr h
    exact ⟨hf, hP⟩

/-- If `v : V ⟶ W` represents the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f`, then `f` is an open immersion if and
only if `v` is an open immersion of algebraic spaces. -/
theorem iff_of_representing {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    OpenImmersion f ↔ AlgebraicSpace.IsOpenImmersion v := by
  constructor
  · intro hf
    exact (representable_and_has_iff_of_representing
      (@AlgebraicSpace.IsOpenImmersion S) f g hv).mp ⟨hf.representable, hf.of_represents⟩
  · intro h
    obtain ⟨hf, hP⟩ := (representable_and_has_iff_of_representing
      (@AlgebraicSpace.IsOpenImmersion S) f g hv).mpr h
    exact ⟨hf, hP⟩

/-- If a morphism of algebraic spaces representing the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is an open immersion, then `f` is an open
immersion. -/
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    AlgebraicSpace.IsOpenImmersion v → OpenImmersion f :=
  (iff_of_representing f g hv).mpr

/-- If `f` is an open immersion, then a morphism of algebraic spaces representing
the 2-fibre product of `g : W.toGroupoids ⟶ Y` against `f` is an open
immersion. -/
theorem covering_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [OpenImmersion f]
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    AlgebraicSpace.IsOpenImmersion v :=
  (iff_of_representing f g hv).mp inferInstance

/-- If `f` is an open immersion, then the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_apex {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [OpenImmersion f] {W : AlgebraicSpace S}
    (g : W.toGroupoids ⟶ Y) [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g] :
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) :=
  (AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_iff_of_covering f g).mp
    (‹OpenImmersion f›.representable)

end OpenImmersion

namespace ClosedImmersion

/-- A morphism of algebraic stacks is a closed immersion if and only if
its base change along a surjective, flat, locally finitely presented morphism
from an algebraic space is represented by a closed immersion of algebraic
spaces. -/
theorem iff_of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    ClosedImmersion f ↔
      ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
        RepresentsTwoFibreProductOnSpace f g V W v ∧
          AlgebraicSpace.IsClosedImmersion v := by
  constructor
  · intro hf
    exact (representable_and_has_iff_exists_covering
      (@AlgebraicSpace.IsClosedImmersion S) f g).mp ⟨hf.representable, hf.of_represents⟩
  · intro h
    obtain ⟨hf, hP⟩ := (representable_and_has_iff_exists_covering
      (@AlgebraicSpace.IsClosedImmersion S) f g).mpr h
    exact ⟨hf, hP⟩

/-- If `v : V ⟶ W` represents the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f`, then `f` is a closed immersion if and
only if `v` is a closed immersion of algebraic spaces. -/
theorem iff_of_representing {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    ClosedImmersion f ↔ AlgebraicSpace.IsClosedImmersion v := by
  constructor
  · intro hf
    exact (representable_and_has_iff_of_representing
      (@AlgebraicSpace.IsClosedImmersion S) f g hv).mp ⟨hf.representable, hf.of_represents⟩
  · intro h
    obtain ⟨hf, hP⟩ := (representable_and_has_iff_of_representing
      (@AlgebraicSpace.IsClosedImmersion S) f g hv).mpr h
    exact ⟨hf, hP⟩

/-- If a morphism of algebraic spaces representing the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is a closed immersion, then `f` is a closed
immersion. -/
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    AlgebraicSpace.IsClosedImmersion v → ClosedImmersion f :=
  (iff_of_representing f g hv).mpr

/-- If `f` is a closed immersion, then a morphism of algebraic spaces representing
the 2-fibre product of `g : W.toGroupoids ⟶ Y` against `f` is a closed
immersion. -/
theorem covering_spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f]
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    AlgebraicSpace.IsClosedImmersion v :=
  (iff_of_representing f g hv).mp inferInstance

/-- If `f` is a closed immersion, then the 2-fibre product of
`g : W.toGroupoids ⟶ Y` against `f` is an algebraic space. -/
theorem isRepresentableByAlgebraicSpace_apex {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [ClosedImmersion f] {W : AlgebraicSpace S}
    (g : W.toGroupoids ⟶ Y) [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g] :
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) :=
  (AlgebraicStack.relativelyRepresentableByAlgebraicSpaces_iff_of_covering f g).mp
    (‹ClosedImmersion f›.representable)

end ClosedImmersion

namespace Immersion

/-- A morphism of algebraic stacks is an immersion if and only if its base
change along a surjective, flat, locally finitely presented morphism from an
algebraic space is represented by an immersion of algebraic spaces. -/
theorem iff_of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    Immersion f ↔
      ∃ (V : AlgebraicSpace S) (v : V ⟶ W),
        RepresentsTwoFibreProductOnSpace f g V W v ∧
          AlgebraicSpace.IsImmersion v := by
  constructor
  · intro hf
    exact (representable_and_has_iff_exists_covering
      (@AlgebraicSpace.IsImmersion S) f g).mp ⟨hf.representable, hf.of_represents⟩
  · intro h
    obtain ⟨hf, hP⟩ := (representable_and_has_iff_exists_covering
      (@AlgebraicSpace.IsImmersion S) f g).mpr h
    exact ⟨hf, hP⟩

end Immersion

end AlgebraicGeometry.Groupoids.Hom
