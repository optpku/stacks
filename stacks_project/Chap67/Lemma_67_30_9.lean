module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Flat
import StacksCheckRecall

/-!
# Flat morphisms of algebraic spaces via the small étale site

A morphism of algebraic spaces is flat if and only if the associated morphism
of small étale ringed topoi is flat.
-/

open CategoryTheory

universe u

/- Lemma 67.30.9: A morphism of algebraic spaces over a scheme is flat if and
only if its associated morphism of small étale ringed sites is flat. -/
@[stacks 073C] #check (AlgebraicGeometry.AlgebraicSpace.flat_iff_isFlatHom :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y), AlgebraicGeometry.AlgebraicSpace.Flat f ↔
      SheafOfModules.RingedSite.IsFlatHom.{u + 1, u, u}
        (AlgebraicGeometry.AlgebraicSpace.commInverseImageStructureSheafMap f))
