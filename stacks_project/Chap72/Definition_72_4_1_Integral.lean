module

public import Mathlib.AlgebraicGeometry.Properties
public import stacks_project.Chap67.Definition_67_47_7_Irreducible
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Integral algebraic spaces

An algebraic space is integral when it is reduced, decent, and its space of
points is irreducible. Decency is required: reduced and irreducible is not
étale-local on algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is integral if it is reduced, decent, and `|X|` is
irreducible. -/
@[mk_iff]
class IsIntegral {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop extends
    IsReduced X, IsDecent X, IsIrreducible X

namespace IsIntegral

/-- An integral algebraic space is reduced, decent, and irreducible. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsIntegral X] :
    IsReduced X ∧ IsDecent X ∧ IsIrreducible X :=
  sorry

/-- Reducedness, decency, and irreducibility together witness that an algebraic
space is integral. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsReduced X] [IsDecent X] [IsIrreducible X] : IsIntegral X :=
  sorry

end IsIntegral

/-- An integral scheme over `S`, viewed as an algebraic space, is integral. -/
instance instIsIntegral_ofOver {S : Scheme.{u}} (T : Over S)
    [AlgebraicGeometry.IsIntegral T.left] : IsIntegral (ofOver T) where
  toIsReduced := instIsReduced_ofOver T
  toIsDecent := instIsDecent_ofOver T
  toIsIrreducible := instIsIrreducible_ofOver T

end AlgebraicGeometry.AlgebraicSpace
