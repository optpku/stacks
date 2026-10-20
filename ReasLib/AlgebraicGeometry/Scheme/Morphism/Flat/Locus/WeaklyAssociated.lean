/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.WeaklyAssociated.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Flat loci over schemes with locally finite weakly associated points

For a locally finite-type morphism, local finiteness of the weakly associated points of the
base makes the pointwise flat locus open. The restriction to this locus is flat and locally
of finite presentation.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a locally finite-type morphism `f : X ⟶ S`, the locus where `f` is flat is open
when the weakly associated points of `S` form a locally finite family. -/
theorem isOpen_flatAt_of_locallyFinite_weakAss
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) :
    IsOpen {x : X | f.flatAt x} := sorry

/-- The open subscheme of points where a locally finite-type morphism is flat. -/
def flatLocus {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) : X.Opens :=
  ⟨{x : X | f.flatAt x}, isOpen_flatAt_of_locallyFinite_weakAss f h_weakAss⟩

/-- Membership in the flat locus of `f` is pointwise flatness of `f`. -/
@[simp]
theorem mem_flatLocus {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) (x : X) :
    x ∈ f.flatLocus h_weakAss ↔ f.flatAt x := sorry

/-- The restriction of a locally finite-type morphism to its flat locus is flat. -/
theorem flatLocus_isFlat
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) :
    Flat ((f.flatLocus h_weakAss).ι ≫ f) := sorry

/-- The restriction of a locally finite-type morphism to its flat locus is locally of finite
presentation. -/
theorem flatLocus_isLocallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))) :
    LocallyOfFinitePresentation ((f.flatLocus h_weakAss).ι ≫ f) := sorry

end AlgebraicGeometry.Scheme.Hom
