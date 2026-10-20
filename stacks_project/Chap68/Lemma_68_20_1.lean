module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.GenericPoints
import StacksCheckRecall

/-!
# Generic points of decent algebraic spaces

On a decent algebraic space, being a generic point of an irreducible component
of `|X|` is equivalent to the same property for every or some étale pointed
chart, to vanishing of the local-ring dimension, and to being a point of
codimension `0`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.20.1: Let `S` be a scheme. Let `X` be a decent algebraic space over
`S`. Let `x ∈ |X|`. The following are equivalent: `x` is a generic point of an
irreducible component of `|X|`; for any étale morphism `(Y, y) ⟶ (X, x)` of
pointed algebraic spaces, `y` is a generic point of an irreducible component of
`|Y|`; for some étale morphism `(Y, y) ⟶ (X, x)` of pointed algebraic spaces,
`y` is a generic point of an irreducible component of `|Y|`; the dimension of
the local ring of `X` at `x` is zero; and `x` is a point of codimension `0` on
`X`.

Here `|X|` is `Points X`, an étale pointed morphism is `Etale f` with
`Points.map f y = x`, generic means membership in `genericPoints`, the
dimension of the local ring is `localRingDimAt`, and a point of codimension `0`
is membership in `codimZeroPoints`. -/
@[stacks 0ABV] #check (AlgebraicGeometry.AlgebraicSpace.mem_genericPoints_tfae :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (x : Points X),
    List.TFAE
      [ x ∈ genericPoints X
      , ∀ (Y : AlgebraicSpace S) (f : Y ⟶ X) (y : Points Y),
          Etale f → Points.map f y = x → y ∈ genericPoints Y
      , ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (y : Points Y),
          Etale f ∧ Points.map f y = x ∧ y ∈ genericPoints Y
      , localRingDimAt x = 0
      , x ∈ codimZeroPoints X ])

/- On a decent algebraic space, a point is generic on `|X|` if and only if the
dimension of the local ring at that point is zero. -/
#check (AlgebraicGeometry.AlgebraicSpace.mem_genericPoints_iff_localRingDimAt_eq_zero :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {x : Points X},
      x ∈ genericPoints X ↔ localRingDimAt x = 0)

/- On a decent algebraic space, a point is generic on `|X|` if and only if it is
a point of codimension `0`. -/
#check (AlgebraicGeometry.AlgebraicSpace.mem_genericPoints_iff_mem_codimZeroPoints :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {x : Points X},
      x ∈ genericPoints X ↔ x ∈ codimZeroPoints X)

/- On a decent algebraic space, a point `x` is generic on `|X|` if and only if
every étale pointed chart `(Y, y) ⟶ (X, x)` has `y` generic on `|Y|`. -/
#check (AlgebraicGeometry.AlgebraicSpace.mem_genericPoints_iff_forall_etale :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {x : Points X},
      x ∈ genericPoints X ↔
        ∀ (Y : AlgebraicSpace S) (f : Y ⟶ X) (y : Points Y),
          Etale f → Points.map f y = x → y ∈ genericPoints Y)

/- On a decent algebraic space, a point `x` is generic on `|X|` if and only if
some étale pointed chart `(Y, y) ⟶ (X, x)` has `y` generic on `|Y|`. -/
#check (AlgebraicGeometry.AlgebraicSpace.mem_genericPoints_iff_exists_etale :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {x : Points X},
      x ∈ genericPoints X ↔
        ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (y : Points Y),
          Etale f ∧ Points.map f y = x ∧ y ∈ genericPoints Y)

/- Membership in `genericPoints` is preserved and reflected by étale morphisms
into a decent algebraic space. -/
#check (AlgebraicGeometry.AlgebraicSpace.mem_genericPoints_map_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X]
      (f : Y ⟶ X) (hf : Etale f) {y : Points Y},
      y ∈ genericPoints Y ↔ Points.map f y ∈ genericPoints X)

end AlgebraicGeometry.AlgebraicSpace
