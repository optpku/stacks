/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

/-!
# Schemes as algebraic spaces

An algebraic space over `S` is a scheme when it is isomorphic to the algebraic
space associated to a scheme over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space over `S` is a scheme if it is representable by a scheme
over `S`. -/
@[mk_iff]
class IsScheme {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- There is a scheme over `S` whose associated algebraic space is isomorphic
  to `X`. -/
  exists_scheme : ∃ (T : Over S), Nonempty (X ≅ ofOver T)

namespace IsScheme

/-- A scheme-like algebraic space is isomorphic to the algebraic space associated
to a scheme over `S`. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsScheme X] :
    ∃ (T : Over S), Nonempty (X ≅ ofOver T) :=
  sorry

/-- An isomorphism with the algebraic space associated to a scheme over `S`
witnesses that an algebraic space is a scheme. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (e : X ≅ ofOver T) : IsScheme X :=
  sorry

/-- Being a scheme is invariant under isomorphism of algebraic spaces. -/
theorem of_iso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (e : X ≅ Y)
    [IsScheme X] : IsScheme Y :=
  sorry

end IsScheme

/-- The algebraic space associated to a scheme over `S` is a scheme. -/
instance instIsScheme_ofOver {S : Scheme.{u}} (T : Over S) : IsScheme (ofOver T) where
  exists_scheme := ⟨T, ⟨Iso.refl (ofOver T)⟩⟩

/-- An algebraic space is a scheme if and only if its functor of points is
representable. -/
theorem isScheme_iff_functorOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsScheme X ↔ X.functorOfPoints.IsRepresentable :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
