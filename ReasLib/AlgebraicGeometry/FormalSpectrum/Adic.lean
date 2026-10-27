/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.AlgebraicGeometry.FormalSpectrum.AlgebraMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage

/-!
# Affine completions of adic rings and their closed fibres

Completion along the topological nilradical and its inverse images give the
affine formal spectrum and closed fibres used over an adic Noetherian base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AffineFormalAlgebraicSpace
  CategoryTheory.Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The completion of `Spec(A)` along `Spec(A ⧸ topologicalNilradical A)`
over `S`. For an adic Noetherian ring, this presents its formal spectrum. -/
abbrev adicSpf {S : Scheme.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] (hA : Spec (.of A) ⟶ S) :
    (Over S)ᵒᵖ ⥤ Type u :=
  completionAlongSubspace (closedImmersion hA (topologicalNilradical A))

/-- `adicSpf hA` is the completion of `Spec(A)` along
`Spec(A ⧸ topologicalNilradical A)`. -/
theorem adicSpf_eq {S : Scheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsAdicRing A]
    (hA : Spec (.of A) ⟶ S) :
    adicSpf hA =
      completionAlongSubspace (closedImmersion hA (topologicalNilradical A)) :=
  rfl

/-- The closed fibre `Z = Y ×_Spec(A) Spec(A ⧸ topologicalNilradical A)` of a
morphism `g : Y ⟶ Spec(A)` of algebraic spaces. -/
abbrev closedFibre {S : Scheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsAdicRing A]
    (hA : Spec (.of A) ⟶ S) {Y : AlgebraicSpace S} (g : Y ⟶ specOver hA) :
    AlgebraicSpace S :=
  inverseImage g (closedImmersion hA (topologicalNilradical A))

/-- The closed immersion of the closed fibre of `g` into `Y`. -/
abbrev closedFibreι {S : Scheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsAdicRing A]
    (hA : Spec (.of A) ⟶ S) {Y : AlgebraicSpace S} (g : Y ⟶ specOver hA) :
    closedFibre hA g ⟶ Y :=
  inverseImageι g (closedImmersion hA (topologicalNilradical A))

/-- The closed fibre of `g` is the inverse image of
`Spec(A ⧸ topologicalNilradical A)`, and `closedFibreι hA g` is the corresponding
closed immersion into `Y`. -/
theorem closedFibre_spec {S : Scheme.{u}} {A : Type u} [CommRing A]
    [TopologicalSpace A] [TopologicalRing.IsAdicRing A]
    (hA : Spec (.of A) ⟶ S) {Y : AlgebraicSpace S} (g : Y ⟶ specOver hA) :
    closedFibre hA g =
        inverseImage g (closedImmersion hA (topologicalNilradical A)) ∧
      closedFibreι hA g =
        inverseImageι g (closedImmersion hA (topologicalNilradical A)) :=
  ⟨rfl, rfl⟩

end AlgebraicGeometry.FormalAlgebraicSpace
