/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.Adic
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FormalModification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace.BaseChange

/-!
# Algebraization of formal modifications after adic formal-spectrum tests

A formal modification of locally Noetherian formal algebraic spaces algebraizes
after an adic test from an adic Noetherian ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AffineFormalAlgebraicSpace
  CategoryTheory.Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Let `S` be a scheme, and let `f : X' ⟶ X` be a formal
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
