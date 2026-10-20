module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Construction

/-!
# Reduced closed subspaces of algebraic spaces

A closed subset `T ⊂ |X|` of the points of an algebraic space is the underlying
point-set of a unique reduced closed subspace `Z ⊂ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 66.12.3: every closed subset of an algebraic space has a reduced closed subspace
structure, unique up to unique isomorphism over the ambient space. -/
@[stacks 03IQ] #check
  (AlgebraicGeometry.AlgebraicSpace.ReducedClosed.Construction.exists_reduced :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (T : TopologicalSpace.Closeds (Points X)),
    ∃ Z : ClosedSubspace X,
      Z.pointsSet = (T : Set (Points X)) ∧
        hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z.X ∧
          ∀ Z' : ClosedSubspace X, Z'.pointsSet = (T : Set (Points X)) →
            hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z'.X →
              ∃! e : Z'.X ≅ Z.X, e.hom ≫ Z.ι = Z'.ι)

/- Any two reduced closed subspaces of `X` with the same underlying point-set admit a unique
morphism over `X`. -/
#check (AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.unique :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {Z Z' : ClosedSubspace X}
    (h_eq : Z.pointsSet = Z'.pointsSet)
    (hZ : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z.X)
    (hZ' : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z'.X),
    ∃! f : Z.X ⟶ Z'.X, f ≫ Z'.ι = Z.ι)
