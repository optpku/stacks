module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow

/-!
# Chow's lemma over a qcqs base

This file packages the diagram supplied by the quasi-compact, quasi-separated form of Chow's
lemma.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A qcqs Chow modification of `f : X ⟶ S` consists of a proper surjective morphism
`π : X' ⟶ X` and an immersion of `X'` into a relative projective space over `S`. -/
structure ChowLemmaQcqsModification {X S : Scheme.{u}} (f : X ⟶ S) where
  /-- The dimension of the chosen relative projective space. -/
  n : ℕ
  /-- The chosen relative projective space over `S`. -/
  P : ProjectiveSpaceOver S n
  /-- The source scheme of the proper surjective morphism. -/
  X' : Scheme.{u}
  /-- The morphism from the source scheme to `X`. -/
  π : X' ⟶ X
  /-- The immersion into the chosen relative projective space. -/
  i : X' ⟶ P.scheme
  /-- The morphism to the relative projective space is an immersion. -/
  isImmersion : IsImmersion i
  /-- The immersion and `π` define the same morphism from `X'` to `S`. -/
  commutes : i ≫ P.hom = π ≫ f
  /-- The morphism `π` is proper. -/
  proper : IsProper π
  /-- The morphism `π` is surjective. -/
  surjective : Surjective π

namespace ChowLemmaQcqsModification

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- The structure morphism from the chosen relative projective space to the base scheme. -/
def p (M : ChowLemmaQcqsModification f) : M.P.scheme ⟶ S :=
  M.P.hom

/-- Constructs a qcqs Chow modification from a relative projective-space immersion and a
proper surjective morphism compatible over the base. -/
def ofProjectiveSpace (n : ℕ) (P : ProjectiveSpaceOver S n) (X' : Scheme.{u})
    (π : X' ⟶ X) (i : X' ⟶ P.scheme) (isImmersion : IsImmersion i)
    (commutes : i ≫ P.hom = π ≫ f) (proper : IsProper π) (surjective : Surjective π) :
    ChowLemmaQcqsModification f where
  n := n
  P := P
  X' := X'
  π := π
  i := i
  isImmersion := isImmersion
  commutes := commutes
  proper := proper
  surjective := surjective

/-- The defining conditions of a qcqs Chow modification are immersion and compatibility over
the base together with properness and surjectivity of `π`. -/
theorem conditions_spec (M : ChowLemmaQcqsModification f) :
    IsImmersion M.i ∧ M.i ≫ M.p = M.π ≫ f ∧ IsProper M.π ∧ Surjective M.π := sorry

/-- A separated finite-type morphism to a quasi-compact, quasi-separated scheme admits a
proper surjective modification whose source immerses into a relative projective space. -/
theorem exists_of_separated_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [Scheme.Hom.FiniteType f] :
    Nonempty (ChowLemmaQcqsModification f) := sorry

end ChowLemmaQcqsModification

end AlgebraicGeometry
