module

public import Mathlib.AlgebraicGeometry.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints

/-!
# Lemma 69.18.1

A weak Chow lemma for algebraic spaces: a separated finite-type algebraic space
over `Spec(A)` admits a proper surjective morphism from a scheme that is
H-quasi-projective over `Spec(A)`.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A weak Chow modification of an algebraic space `X` over `Spec(A)` consists of a
scheme `X'` over `Spec(A)` together with a proper surjective morphism
`π : ofOver X' ⟶ X` whose structure morphism is H-quasi-projective. -/
structure WeakChowModification {A : Type u} [CommRing A]
    (X : AlgebraicSpace (Spec (CommRingCat.of A))) where
  /-- The scheme over `Spec(A)` supplying the modification. -/
  X' : Over (Spec (CommRingCat.of A))
  /-- The morphism from that scheme, viewed as an algebraic space, to `X`. -/
  π : ofOver X' ⟶ X
  /-- The morphism `π` is proper. -/
  proper : Proper π
  /-- The morphism `π` is surjective. -/
  surjective : Surjective π
  /-- The structure morphism of `X'` is H-quasi-projective. -/
  hQuasiProjective : HQuasiProjective X'.hom

namespace WeakChowModification

variable {A : Type u} [CommRing A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}

/-- Constructs a weak Chow modification from a scheme over `Spec(A)` and a proper
surjective morphism whose structure morphism is H-quasi-projective. -/
def of (X' : Over (Spec (CommRingCat.of A))) (π : ofOver X' ⟶ X) (proper : Proper π)
    (surjective : Surjective π) (hQuasiProjective : HQuasiProjective X'.hom) :
    WeakChowModification X where
  X' := X'
  π := π
  proper := proper
  surjective := surjective
  hQuasiProjective := hQuasiProjective

/-- A weak Chow modification is a proper surjective morphism from a scheme that is
H-quasi-projective over `Spec(A)`. -/
theorem conditions_spec (M : WeakChowModification X) :
    Proper M.π ∧ Surjective M.π ∧ HQuasiProjective M.X'.hom :=
  sorry

/-- Lemma 69.18.1: If `A` is a ring and `X` is an algebraic space over `Spec(A)`
whose structure morphism is separated of finite type, then there exists a proper
surjective morphism `X' ⟶ X` from a scheme `X'` that is H-quasi-projective over
`Spec(A)`. -/
@[stacks 089J]
theorem exists_of_separated_finiteType (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    [Separated (toBase X)] [FiniteType (toBase X)] :
    Nonempty (WeakChowModification X) :=
  sorry

end WeakChowModification

end AlgebraicGeometry.AlgebraicSpace

