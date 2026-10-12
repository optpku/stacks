/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap78.Definition_78_19_1_QuotientSheaf

/-!
# Representable quotients of pre-relations on algebraic spaces

This module records when the fppf quotient sheaf of a pre-relation (or of a groupoid in
algebraic spaces) is an algebraic space or is representable by a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- A pre-relation has a quotient representable by an algebraic space when the fppf
quotient sheaf `U/R` is isomorphic to the universe-raised sheaf of an algebraic space
over `S`. -/
abbrev HasAlgebraicSpaceQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) : Prop :=
  ∃ M : AlgebraicSpace S, Nonempty (uliftSheaf M ≅ P.quotientSheaf)

/-- A pre-relation has a representable quotient when the underlying presheaf of the fppf
quotient sheaf `U/R` is representable by a scheme over `S`. -/
abbrev HasRepresentableQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) : Prop :=
  (P.quotientSheaf).obj.IsRepresentable

/-- Having a quotient representable by an algebraic space means the quotient sheaf is
isomorphic to `uliftSheaf M` for some algebraic space `M` over `S`. -/
theorem hasAlgebraicSpaceQuotient_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    HasAlgebraicSpaceQuotient P ↔
      ∃ M : AlgebraicSpace S, Nonempty (uliftSheaf M ≅ P.quotientSheaf) :=
  sorry

/-- Having a representable quotient means the underlying presheaf of the quotient sheaf is
representable. -/
theorem hasRepresentableQuotient_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    HasRepresentableQuotient P ↔ (P.quotientSheaf).obj.IsRepresentable :=
  sorry

/-- A pre-relation has a representable quotient if and only if the quotient sheaf is
isomorphic to the universe-raised sheaf of `ofOver T` for some scheme `T` over `S`. -/
theorem hasRepresentableQuotient_iff_exists_ofOver {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) :
    HasRepresentableQuotient P ↔
      ∃ T : Over S, Nonempty (uliftSheaf (ofOver T) ≅ P.quotientSheaf) :=
  sorry

/-- A representable quotient is in particular a quotient representable by an algebraic
space. -/
theorem hasAlgebraicSpaceQuotient_of_hasRepresentableQuotient {S : Scheme.{u}}
    {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)
    (h : HasRepresentableQuotient P) : HasAlgebraicSpaceQuotient P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A groupoid in algebraic spaces has a quotient representable by an algebraic space
when the quotient of the underlying pre-relation `j = (t, s)` is an algebraic space. -/
abbrev HasAlgebraicSpaceQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : Prop :=
  G.toPreRelation.HasAlgebraicSpaceQuotient

/-- A groupoid in algebraic spaces has a representable quotient when the quotient of the
underlying pre-relation `j = (t, s)` is representable by a scheme. -/
abbrev HasRepresentableQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : Prop :=
  G.toPreRelation.HasRepresentableQuotient

/-- A groupoid in algebraic spaces has a quotient representable by an algebraic space if
and only if its underlying pre-relation `j = (t, s)` does. -/
theorem hasAlgebraicSpaceQuotient_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    HasAlgebraicSpaceQuotient G ↔ G.toPreRelation.HasAlgebraicSpaceQuotient :=
  sorry

/-- A groupoid in algebraic spaces has a representable quotient if and only if its
underlying pre-relation `j = (t, s)` does. -/
theorem hasRepresentableQuotient_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    HasRepresentableQuotient G ↔ G.toPreRelation.HasRepresentableQuotient :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
