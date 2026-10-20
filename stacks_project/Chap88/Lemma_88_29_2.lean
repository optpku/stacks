/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.RingTheory.Topology.Adic.Complete
public import stacks_project.Chap88.Definition_88_24_1_Modification
public import stacks_project.Chap88.Lemma_88_21_9

/-!
# Algebraization of formal modifications after adic `Spf` tests

A formal modification of locally Noetherian formal algebraic spaces over a
scheme `S` algebraizes after any adic test from the formal spectrum of an adic
Noetherian ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AffineFormalAlgebraicSpace
  CategoryTheory.Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- If a section of `X'` fppf-locally factors through an infinitesimal
neighbourhood of the inverse image of `i` along `f : X' ⟶ X`, then
postcomposition with `f` fppf-locally factors through an infinitesimal
neighbourhood of `i`. -/
theorem fppfLocallyFactorsThroughNeighbourhood_comp {S : Scheme.{u}}
    {X' X Z : AlgebraicSpace S} (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {U : (Over S)ᵒᵖ} {x : X'.functorOfPoints.obj U}
    (hx : fppfLocallyFactorsThroughNeighbourhood (inverseImageι f i) x) :
    fppfLocallyFactorsThroughNeighbourhood i (f.app U x) :=
  sorry

namespace completionAlongSubspace

/-- The morphism of completions induced by `f : X' ⟶ X` along the inverse image
closed subspace `Z' = f⁻¹(Z)` given by `inverseImageι f i`. -/
def map {S : Scheme.{u}} {X' X Z : AlgebraicSpace S} (f : X' ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    completionAlongSubspace (inverseImageι f i) ⟶ completionAlongSubspace i where
  app U :=
    ofHom fun x ↦
      ⟨f.app U x.1, fppfLocallyFactorsThroughNeighbourhood_comp f i x.property⟩
  naturality := sorry

/-- The underlying section of `map f i` is the component of `f`. -/
theorem map_app {S : Scheme.{u}} {X' X Z : AlgebraicSpace S} (f : X' ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : (Over S)ᵒᵖ)
    (x : (completionAlongSubspace (inverseImageι f i)).obj U) :
    (ι i).app U ((map f i).app U x) =
      f.app U ((ι (inverseImageι f i)).app U x) :=
  sorry

end completionAlongSubspace

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The formal spectrum `Spf(A)` of an adic ring `A` over `S`, as the completion
of `Spec(A)` along `Spec(A ⧸ topologicalNilradical A)`. -/
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
  sorry

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
  sorry

/-- Lemma 88.29.2: let `S` be a scheme, and let `f : X' ⟶ X` be a formal
modification of locally Noetherian formal algebraic spaces over `S`. Given an
adic Noetherian topological ring `A` and an adic morphism `p : adicSpf hA ⟶ X`,
there exists a proper morphism `g : Y ⟶ specOver hA` of algebraic spaces and an
isomorphism `pullback f p ≅ completionAlongSubspace (closedFibreι hA g)` over
`adicSpf hA`, where the closed fibre is
`Y ×_Spec(A) Spec(A ⧸ topologicalNilradical A)`. -/
@[stacks 0GDV]
theorem exists_proper_of_adicSpf {S : Scheme.{u}}
    {X X' : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace X']
    [IsLocallyNoetherian X] [IsLocallyNoetherian X']
    (f : X' ⟶ X) [LocallyOfFiniteType f] [FormalModification f]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
    (hA : Spec (.of A) ⟶ S) (p : adicSpf hA ⟶ X)
    (hp : AlgebraicSpace.representableByAlgebraicSpaces p) :
    ∃ (Y : AlgebraicSpace S) (g : Y ⟶ specOver hA)
      (e : pullback f p ≅ completionAlongSubspace (closedFibreι hA g)),
      AlgebraicSpace.Proper g ∧
        e.hom ≫ completionAlongSubspace.map g
            (closedImmersion hA (topologicalNilradical A)) =
          pullback.snd f p :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
