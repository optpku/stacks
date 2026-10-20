module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.Diagonal
import StacksCheckRecall

/-!
# Separatedness via the relative diagonal

A morphism of algebraic spaces is separated iff its relative diagonal is
universally closed, iff that same diagonal is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.40.9: separatedness is equivalent to universal closedness and
properness of the relative diagonal. -/
@[stacks 04Y0] #check (AlgebraicGeometry.AlgebraicSpace.Separated.tfae_diagonal :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE [Separated f, UniversallyClosed (pullback.diagonal f),
      Proper (pullback.diagonal f)])
