module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Locus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory Limits

universe u

/- Lemma 29.30.12: for a locally finite-type morphism, the closed-fiber complete-intersection
locus commutes with arbitrary base change. If the morphism is flat and locally finitely presented,
the same is true of its open syntomic locus. -/
@[stacks 02V3] #check
  (AlgebraicGeometry.Scheme.Hom.fiberCompleteIntersectionLocus_pullback_snd :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S),
      (pullback.snd f g).fiberCompleteIntersectionLocus =
        (pullback.fst f g) ⁻¹' f.fiberCompleteIntersectionLocus)

#check
  (AlgebraicGeometry.Scheme.Hom.syntomicLocus_pullback_snd :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      (g : S' ⟶ S),
      (pullback.snd f g).syntomicLocus =
        (pullback.fst f g) ⁻¹ᵁ f.syntomicLocus)

#check
  (AlgebraicGeometry.Scheme.Hom.syntomicAt_iff_of_pullback_snd :
    ∀ {X S S' : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
      (g : S' ⟶ S) (x' : (pullback f g : Scheme)),
      SyntomicAt (pullback.snd f g) x' ↔
        SyntomicAt f ((pullback.fst f g) x'))
