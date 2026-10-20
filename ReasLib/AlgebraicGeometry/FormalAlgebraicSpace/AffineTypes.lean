/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic
public import ReasLib.AlgebraicGeometry.FormalSpectrum.PowerStages
public import ReasLib.RingTheory.Topology.Adic.Complete

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AffineFormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- An affine formal space is adic* if it has a compatible quotient-power presentation
by a finitely generated ideal of definition in an adic ring. -/
@[mk_iff] class IsAdicStarAffine {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- An adic ring and its canonical quotient-power diagram present the formal space. -/
  exists_adicStar :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsAdicRing A) (I : Ideal A) (_ : I.FG)
      (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (structureHom : Spec (.of A) ⟶ S),
        IsDirectedAffineThickeningColimit (powerThickenings structureHom I) X

/-- An affine scheme represents an adic* formal space with its discrete presentation. -/
instance IsAdicStarAffine.instYoneda {S : Scheme.{u}} (U : Over S) [IsAffine U.left] :
    IsAdicStarAffine (yoneda.obj U) := sorry

/-- An affine formal space is Noetherian if it has a compatible quotient-power
presentation by an ideal of definition in an adic Noetherian ring. -/
@[mk_iff] class IsNoetherianAffine {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- An adic Noetherian ring and its canonical quotient-power diagram present the space. -/
  exists_adicNoetherian :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsAdicRing A) (_ : IsNoetherianRing A)
      (I : Ideal A) (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (structureHom : Spec (.of A) ⟶ S),
        IsDirectedAffineThickeningColimit (powerThickenings structureHom I) X

/-- A Noetherian affine scheme represents a Noetherian formal space. -/
instance IsNoetherianAffine.instYoneda {S : Scheme.{u}} (U : Over S)
    [IsAffine U.left] [IsNoetherian U.left] :
    IsNoetherianAffine (yoneda.obj U) := sorry

namespace IsAdicStarAffine

/-- An adic* presentation uses the actual compatible quotient-power diagram. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsAdicStarAffine X] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsAdicRing A) (I : Ideal A) (_ : I.FG)
      (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (structureHom : Spec (.of A) ⟶ S),
        IsDirectedAffineThickeningColimit (powerThickenings structureHom I) X :=
  ‹IsAdicStarAffine X›.exists_adicStar

/-- Characterization by an adic ring and its compatible quotient-power presentation. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsAdicStarAffine X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsAdicRing A) (I : Ideal A) (_ : I.FG)
        (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
        (structureHom : Spec (.of A) ⟶ S),
          IsDirectedAffineThickeningColimit (powerThickenings structureHom I) X :=
  ⟨fun h ↦ h.exists_adicStar, fun h ↦ ⟨h⟩⟩

/-- A diagram identifies an adic* space when its structure and transition maps
are compatible with the canonical quotient-power diagram. -/
theorem of {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] (I : Ideal A) (hI : I.FG)
    (hdef : TopologicalRing.Ideal.IsIdealOfDefinition I)
    (structureHom : Spec (.of A) ⟶ S) (D : ℕ ⥤ Over S)
    (e : D ≅ powerThickenings structureHom I)
    (hcolim : IsDirectedAffineThickeningColimit D X) :
    IsAdicStarAffine X :=
  ⟨⟨A, inferInstance, inferInstance, inferInstance, I, hI, hdef, structureHom,
    IsDirectedAffineThickeningColimit.of_iso e hcolim⟩⟩

end IsAdicStarAffine

namespace IsNoetherianAffine

/-- A Noetherian affine formal space has an actual quotient-power presentation. -/
theorem spec {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsNoetherianAffine X] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : TopologicalRing.IsAdicRing A) (_ : IsNoetherianRing A)
      (I : Ideal A) (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
      (structureHom : Spec (.of A) ⟶ S),
        IsDirectedAffineThickeningColimit (powerThickenings structureHom I) X :=
  ‹IsNoetherianAffine X›.exists_adicNoetherian

/-- Characterization by the compatible power diagram of an adic Noetherian ring. -/
theorem iff {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsNoetherianAffine X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsAdicRing A) (_ : IsNoetherianRing A)
        (I : Ideal A) (_ : TopologicalRing.Ideal.IsIdealOfDefinition I)
        (structureHom : Spec (.of A) ⟶ S),
          IsDirectedAffineThickeningColimit (powerThickenings structureHom I) X :=
  ⟨fun h ↦ h.exists_adicNoetherian, fun h ↦ ⟨h⟩⟩

/-- The adic-diagram presentation records the same stages and maps, with the
defining ideal's adic topology and completeness made explicit. -/
theorem iff_adicDiagram {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) :
    IsNoetherianAffine X ↔
      ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
        (_ : TopologicalRing.IsAdicRing A) (_ : IsNoetherianRing A)
        (I : Ideal A) (_ : IsAdic I ∧ IsAdicComplete I A)
        (structureHom : Spec (.of A) ⟶ S),
          IsDirectedAffineThickeningColimit (AdicPresentation.diagram structureHom I) X :=
  by
    constructor
    · intro h
      obtain ⟨A, hRing, hTop, hAdic, hNoetherian, I, hI, structureHom, hcolim⟩ :=
        h.exists_adicNoetherian
      letI := hRing
      letI := hTop
      letI := hAdic
      letI := hNoetherian
      exact ⟨A, hRing, hTop, hAdic, hNoetherian, I,
        ⟨hI.isAdic, hI.isAdicComplete⟩, structureHom, hcolim⟩
    · rintro ⟨A, hRing, hTop, hAdic, hNoetherian, I, hI, structureHom, hcolim⟩
      letI := hRing
      letI := hTop
      letI := hAdic
      letI := hNoetherian
      exact ⟨⟨A, hRing, hTop, hAdic, hNoetherian, I,
        TopologicalRing.Ideal.isIdealOfDefinition_of_isAdic hI.1, structureHom, hcolim⟩⟩

end IsNoetherianAffine

end AlgebraicGeometry.FormalAlgebraicSpace
