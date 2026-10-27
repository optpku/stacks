/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FormalModification.Algebraization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AffineFormalAlgebraicSpace
  CategoryTheory.Limits Opposite TypeCat

universe u

/- Lemma 88.29.2: A formal modification of locally Noetherian formal algebraic
spaces algebraizes after any adic formal-spectrum test from an adic Noetherian
ring, with the isomorphism over the test formal spectrum. -/
@[stacks 0GDV] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.exists_proper_of_adicSpf :
   ∀ {S : Scheme.{u}}
    {X X' : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace X']
    [IsLocallyNoetherian X] [IsLocallyNoetherian X']
    (f : X' ⟶ X) [LocallyOfFiniteType f] [FormalModification f]
    {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
    (hA : Spec (.of A) ⟶ S) (p : adicSpf hA ⟶ X)
    (hp : AlgebraicSpace.representableByAlgebraicSpaces p),
    ∃ (Y : AlgebraicSpace S) (g : Y ⟶ specOver hA)
      (e : pullback f p ≅ completionAlongSubspace (closedFibreι hA g)),
      AlgebraicSpace.Proper g ∧
        e.hom ≫ completionAlongSubspace.map g
            (closedImmersion hA (topologicalNilradical A)) =
          pullback.snd f p)
