module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified.EtaleLocal
import StacksCheckRecall

/-!
# Étale scheme-square characterizations of formal unramifiedness

A morphism of algebraic spaces is formally unramified if and only if every
commutative square with étale vertical arrows from schemes has formally
unramified top arrow in the sense of Definition 37.6.1, and if and only if
some such square with surjective vertical arrows does.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallyUnramified

/- Lemma 76.14.2 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is formally unramified if and only if, for
every commutative square with étale vertical arrows from schemes, the top
arrow is formally unramified as a morphism of schemes in the sense of
Definition 37.6.1. -/
@[stacks 04G8]
#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.iff_forall_etaleSchemeSquare :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    FormallyUnramified f ↔
      ∀ {U V : Over S} (h : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
        [Etale a] [Etale b], CommSq (ofOverMap h) a b f →
          AlgebraicGeometry.FormallyUnramified h.left)

/- Lemma 76.14.2 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is formally unramified if and only if there
is a commutative square with étale surjective vertical arrows from schemes
whose top arrow is formally unramified as a morphism of schemes in the sense
of Definition 37.6.1. -/
@[stacks 04G8]
#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.iff_exists_surjectiveEtaleSchemeSquare :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    FormallyUnramified f ↔
      ∃ (U V : Over S) (h : U ⟶ V) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y),
        Etale a ∧ Etale b ∧ Function.Surjective (Points.map a) ∧
          Function.Surjective (Points.map b) ∧ CommSq (ofOverMap h) a b f ∧
            AlgebraicGeometry.FormallyUnramified h.left)

/- A formally unramified morphism of algebraic spaces has formally unramified
top arrow on every commutative square with étale vertical arrows from schemes. -/
#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.etaleSchemeSquare :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {U V : Over S} {h : U ⟶ V} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y}
    {f : X ⟶ Y} [FormallyUnramified f] [Etale a] [Etale b]
    (sq : CommSq (ofOverMap h) a b f),
      AlgebraicGeometry.FormallyUnramified h.left)

/- A morphism of algebraic spaces is formally unramified as soon as some
commutative square with étale surjective vertical arrows from schemes has
formally unramified top arrow. -/
#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.of_surjectiveEtaleSchemeSquare :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {U V : Over S} {h : U ⟶ V} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y} {f : X ⟶ Y}
    [Etale a] [Etale b]
    (ha_surjective : Function.Surjective (Points.map a))
    (hb_surjective : Function.Surjective (Points.map b))
    [AlgebraicGeometry.FormallyUnramified h.left]
    (sq : CommSq (ofOverMap h) a b f), FormallyUnramified f)

/- On a commutative square with étale surjective vertical arrows from schemes,
space-level formal unramifiedness of the bottom arrow is equivalent to
scheme-level formal unramifiedness of the top arrow. -/
#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.iff_of_surjectiveEtaleSchemeSquare :
    ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {U V : Over S} {h : U ⟶ V} {a : ofOver U ⟶ X}
    {b : ofOver V ⟶ Y} {f : X ⟶ Y} [Etale a] [Etale b]
    (ha_surjective : Function.Surjective (Points.map a))
    (hb_surjective : Function.Surjective (Points.map b))
    (sq : CommSq (ofOverMap h) a b f),
      FormallyUnramified f ↔ AlgebraicGeometry.FormallyUnramified h.left)

end AlgebraicGeometry.AlgebraicSpace.FormallyUnramified
