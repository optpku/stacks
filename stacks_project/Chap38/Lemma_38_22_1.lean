/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Artinian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 38.22.1: over the spectrum of an Artinian ring, the flattening functor of a
quasicoherent module has a representing scheme whose structure morphism is a closed immersion. -/
@[stacks 05PB] #check
  (AlgebraicGeometry.Scheme.Modules.Flattening.exists_closedImmersion_representation :
    ∀ {R : Type u} [CommRing R] [IsArtinianRing R] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of R)) (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      ∃ S' : Over (Spec (CommRingCat.of R)),
        Nonempty
          ((AlgebraicGeometry.Scheme.Modules.Flattening.functor f ℱ).RepresentableBy S') ∧
            IsClosedImmersion S'.hom)
