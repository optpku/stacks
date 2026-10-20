module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
import StacksCheckRecall

/-!
# Codimension versus local-ring dimension on decent algebraic spaces

On a decent algebraic space, the topological codimension of an irreducible
closed subset of `Points X` equals the dimension of the local ring at its
generic point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.20.2: Let `S` be a scheme. Let `X` be a decent algebraic space
over `S`. Let `T ⊂ |X|` be an irreducible closed subset. Let `ξ ∈ T` be the
generic point (Proposition 68.12.4). Then `codim(T, |X|)` (Topology,
Definition 5.11.1) is the dimension of the local ring of `X` at `ξ`
(Properties of Spaces, Definition 66.10.2).

Here `|X|` is `Points X`, an irreducible closed subset is
`T : IrreducibleCloseds (Points X)`, the generic point is `IsGenericPoint ξ T`,
`codim(T, |X|)` is `Order.coheight T`, and the dimension of the local ring is
`localRingDimAt`. -/
@[stacks 0ED1] #check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_eq_coheight :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (T : IrreducibleCloseds (Points X)) (ξ : Points X), IsGenericPoint ξ T →
    localRingDimAt ξ = Order.coheight T)

#check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_genericPoint_eq_coheight :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (T : IrreducibleCloseds (Points X)),
    localRingDimAt T.isIrreducible.genericPoint = Order.coheight T)

#check (AlgebraicGeometry.AlgebraicSpace.localRingDimAt_eq_coheight_mk :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {T : Set (Points X)}
    (hT_irred : IsIrreducible T) (hT_closed : IsClosed T) (ξ : Points X),
    IsGenericPoint ξ T →
    localRingDimAt ξ = Order.coheight (IrreducibleCloseds.mk T hT_irred hT_closed))

end AlgebraicGeometry.AlgebraicSpace
