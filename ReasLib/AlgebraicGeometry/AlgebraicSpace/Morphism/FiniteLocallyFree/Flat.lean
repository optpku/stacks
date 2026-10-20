/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

/-!
# Finite locally free and finite flat morphisms of algebraic spaces

A morphism of algebraic spaces is finite locally free if and only if it is
finite, flat, and locally of finite presentation. Over a locally Noetherian
target, finite plus flat is equivalent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FiniteLocallyFree

/-- A morphism of algebraic spaces is finite locally free if and only if it is
finite, flat, and locally of finite presentation. -/
theorem iff_isFinite_and_flat_and_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FiniteLocallyFree f ↔ IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f :=
  sorry

/-- A morphism of algebraic spaces with locally Noetherian target is finite
locally free if and only if it is finite and flat. -/
theorem iff_isFinite_and_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] :
    FiniteLocallyFree f ↔ IsFinite f ∧ Flat f :=
  sorry

/-- A finite locally free morphism of algebraic spaces is finite. -/
instance instIsFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [h : FiniteLocallyFree f] : IsFinite f :=
  ((iff_isFinite_and_flat_and_locallyOfFinitePresentation f).mp h).1

/-- A finite locally free morphism of algebraic spaces is flat. -/
instance instFlat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [h : FiniteLocallyFree f] : Flat f :=
  ((iff_isFinite_and_flat_and_locallyOfFinitePresentation f).mp h).2.1

/-- A finite locally free morphism of algebraic spaces is locally of finite
presentation. -/
instance instLocallyOfFinitePresentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [h : FiniteLocallyFree f] :
    LocallyOfFinitePresentation f :=
  ((iff_isFinite_and_flat_and_locallyOfFinitePresentation f).mp h).2.2

/-- A finite, flat, and locally of finite presentation morphism of algebraic
spaces is finite locally free. -/
instance of_isFinite_of_flat_of_locallyOfFinitePresentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [hfinite : IsFinite f] [hflat : Flat f]
    [hpresentation : LocallyOfFinitePresentation f] : FiniteLocallyFree f :=
  (iff_isFinite_and_flat_and_locallyOfFinitePresentation f).mpr
    ⟨hfinite, hflat, hpresentation⟩

/-- Over a locally Noetherian target, a finite and flat morphism of algebraic
spaces is finite locally free. -/
instance of_isFinite_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [hfinite : IsFinite f] [hflat : Flat f] :
    FiniteLocallyFree f :=
  (iff_isFinite_and_flat f).mpr ⟨hfinite, hflat⟩

end FiniteLocallyFree

end AlgebraicGeometry.AlgebraicSpace
