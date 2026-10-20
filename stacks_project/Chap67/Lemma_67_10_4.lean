module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Monomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 67.10.4: a composition of monomorphisms is a monomorphism. -/
@[stacks 042O] #check
  (AlgebraicGeometry.AlgebraicSpace.monomorphisms_isStableUnderComposition :
    ∀ {S : Scheme.{u}}, (monomorphisms (AlgebraicSpace S)).IsStableUnderComposition)
