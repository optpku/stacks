module

public import ReasLib.RingTheory.RingHom.Perfect.CompleteIntersection
import StacksCheckRecall

@[expose] public section

universe u v

/-!
# Lemma 15.83.6

@stack 07EN

The source-faithful statement is the ring-map property implication.  The polynomial presentation,
Koszul-regular kernel, and finite-resolution argument are proof infrastructure owned by the
ReasLib leaf rather than chapter-local declarations.
-/

/- Lemma 15.83.6, tag `07EN`: a local complete intersection homomorphism is perfect. -/
@[stacks 07EN "local complete-intersection homomorphisms are perfect"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f : A →+* B} (h : f.IsLocalCompleteIntersection) =>
  (h.isPerfectRingMap : f.IsPerfectRingMap)

/- The corresponding canonical instance is available for downstream typeclass search. -/
@[stacks 07EN "perfect instance of a local complete-intersection homomorphism"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) [f.IsLocalCompleteIntersection] =>
  (inferInstance : f.IsPerfectRingMap)
