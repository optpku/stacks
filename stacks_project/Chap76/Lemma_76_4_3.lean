module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Monomorphism
import StacksCheckRecall

/-!
# Quasi-compact flat surjective monomorphisms of algebraic spaces

A quasi-compact flat surjective monomorphism of algebraic spaces is an
isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.4.3: A quasi-compact flat surjective monomorphism of algebraic
spaces is an isomorphism. -/
@[stacks 0B8C] #check
  (AlgebraicGeometry.AlgebraicSpace.isIso_of_quasiCompact_flat_surjective_mono :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [Flat f] [Surjective f] [Mono f], IsIso f)

end AlgebraicGeometry.AlgebraicSpace
