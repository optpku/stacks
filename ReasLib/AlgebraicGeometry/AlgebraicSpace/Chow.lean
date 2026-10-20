module

public import Mathlib.AlgebraicGeometry.Spec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ProjectiveSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible

/-!
# Chow's lemma for finite-type algebraic spaces

A separated finite-type morphism of algebraic spaces into a quasi-compact,
absolutely quasi-separated algebraic space admits a proper surjective
approximation that open-immerses into a proper representable algebraic space
over the same base.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated finite-type morphism of algebraic spaces to a quasi-compact,
absolutely quasi-separated algebraic space admits a proper surjective morphism
`g : X' ⟶ X` and an open immersion `j : X' ⟶ Xbar'`, where `Xbar'` is proper
and representable over the target via `p` and `g ≫ f = j ≫ p`. -/
theorem exists_isOpenImmersion_proper_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [FiniteType f] [Separated f] :
    ∃ (X' Xbar' : AlgebraicSpace S) (g : X' ⟶ X) (j : X' ⟶ Xbar')
      (p : Xbar' ⟶ Y),
      Proper g ∧ Surjective g ∧ IsOpenImmersion j ∧ Proper p ∧
        yoneda.relativelyRepresentable p ∧ g ≫ f = j ≫ p :=
  sorry

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

/-- If `A` is a ring and `X` is an algebraic space over `Spec(A)`
whose structure morphism is separated of finite type, then there exists a proper
surjective morphism `X' ⟶ X` from a scheme `X'` that is H-quasi-projective over
`Spec(A)`. -/
@[stacks 089J]
theorem exists_of_separated_finiteType (X : AlgebraicSpace (Spec (CommRingCat.of A)))
    [Separated (SchemeRealization.toBase X)] [FiniteType (SchemeRealization.toBase X)] :
    Nonempty (WeakChowModification X) :=
  sorry

end WeakChowModification

/-- A separated finite-type morphism of algebraic spaces to an absolutely separated,
quasi-compact algebraic space admits a proper surjective morphism `g : X' ⟶ X`
and an immersion `i : X' ⟶ ProjectiveSpace n Y` for some `n`, with
`g ≫ f = i ≫ ProjectiveSpace.toBase n Y`. -/
@[stacks 089M]
theorem exists_proper_surjective_isImmersion
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [Separated f] [IsAbsolutelySeparated Y] [IsQuasiCompact Y] :
    ∃ (n : ℕ) (X' : AlgebraicSpace S) (g : X' ⟶ X)
      (i : X' ⟶ ProjectiveSpace n Y),
      Proper g ∧ Surjective g ∧ IsImmersion i ∧
        g ≫ f = i ≫ ProjectiveSpace.toBase n Y :=
  sorry

/-- A separated finite-type morphism of algebraic spaces to an absolutely separated,
Noetherian algebraic space admits a blowup admissible over a dense open of its source
and an immersion of the blowup into a relative projective space, compatible with the
morphism to the target. -/
@[stacks 088U]
theorem exists_dense_open_isAdmissibleBlowup_isImmersion
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Separated f]
    [IsAbsolutelySeparated Y] [IsNoetherian Y] :
    ∃ (U : OpenSubspace X) (n : ℕ) (X' : AlgebraicSpace S)
      (bX : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n Y),
      Dense (U.pointsSet : Set (Points X)) ∧
        IsAdmissibleBlowup U bX ∧ IsImmersion i ∧
        bX ≫ f = i ≫ ProjectiveSpace.toBase n Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
