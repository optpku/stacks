module

public import ReasLib.NumberTheory.AlgebraicNumbers

/-!
# Artin–Schreier finite subgroups of the rational absolute Galois group

The concrete fields and Galois classification are provided by the number-theory owner.
The original field and Galois-group names remain definitionally equal compatibility names.
-/

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

/-- The relative algebraic closure of the rationals in the complex numbers. -/
abbrev algebraicQ : Type := AlgebraicNumbers.algebraicQ

/-- The group of rational algebra automorphisms of the complex algebraic numbers. -/
abbrev gal : Type := AlgebraicNumbers.gal

end AlgebraicGeometry.AlgebraicSpace.AlgebraicClosureQuotient

#check (AlgebraicNumbers.realIntersection :
  IntermediateField ℚ AlgebraicNumbers.algebraicQ)

#check (AlgebraicNumbers.complexConj_apply :
  ∀ x : AlgebraicNumbers.algebraicQ,
    (AlgebraicNumbers.complexConj x : ℂ) = starRingEnd ℂ (x : ℂ))

#check (AlgebraicNumbers.complexConjSubgroup_eq_fixingSubgroup :
  AlgebraicNumbers.complexConjSubgroup = AlgebraicNumbers.realIntersection.fixingSubgroup)

#check (AlgebraicNumbers.finite_subgroup_eq_bot_or_isConj :
  ∀ (H : Subgroup AlgebraicNumbers.gal) [Finite H],
    H = ⊥ ∨ ∃ g : AlgebraicNumbers.gal,
      H = AlgebraicNumbers.complexConjSubgroup.map (MulAut.conj g).toMonoidHom)
