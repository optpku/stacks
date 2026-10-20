module

public import stacks_project.Chap68.Definition_68_11_2_ResidueField
import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField
import StacksCheckRecall

/-!
# Identifying residue fields along a morphism of decent algebraic spaces

A morphism of decent algebraic spaces induces a homomorphism of residue fields at a
point, recorded as a factorization of the composite `Spec(κ(x)) ⟶ Y` through
`Spec(κ(f(x))) ⟶ Y`. That homomorphism is an isomorphism if and only if the
composite is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open FieldValuedPoint

/- Lemma 68.11.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of decent
algebraic spaces over `S`. Let `x` be a point of `X` with image `y = Points.map f x`.
The following are equivalent: `f` induces an isomorphism `κ(y) ⟶ κ(x)`, and the
induced morphism `Spec(κ(x)) ⟶ Y` is a monomorphism.

The induced field homomorphism is the source-spectrum map of a factorization of
`(residuePoint x).map f` through `residuePoint (Points.map f x)`. -/
@[stacks 0EMX] #check (AlgebraicGeometry.AlgebraicSpace.identifiesResidueFields_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X)
    (φ : Factorization ((residuePoint x).map f) (residuePoint (Points.map f x))),
    IsIso φ.schemeHom ↔ Mono (X.fromSpecResidueField x ≫ f))

end AlgebraicGeometry.AlgebraicSpace
