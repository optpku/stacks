module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine.Coprod

/-- The coproduct of two standard projective lines over a field. -/
abbrev scheme (k : Type u) [Field k] : Scheme.{u} :=
  coprod (ProjectiveLine.scheme k) (ProjectiveLine.scheme k)

/-- The structure morphism of the coproduct of two projective lines to `Spec k`. -/
abbrev toSpec (k : Type u) [Field k] : scheme k ⟶ Spec (.of k) :=
  coprod.desc (ProjectiveLine.toSpec k) (ProjectiveLine.toSpec k)

/-- The coproduct of two projective lines over a field is nonempty. -/
instance instNonempty (k : Type u) [Field k] : Nonempty (scheme k) := sorry

/-- The coproduct of two projective lines over a field is not irreducible. -/
theorem not_irreducible (k : Type u) [Field k] :
    ¬ IrreducibleSpace (scheme k) := sorry

/-- The coproduct of two projective lines admits a closed immersion into projective
three-space commuting with the structure morphisms to `Spec k`. -/
theorem exists_closedImmersion (k : Type u) [Field k] :
    ∃ immersion : scheme k ⟶ ProjectiveSpace.scheme k 3,
      IsClosedImmersion immersion ∧
        immersion ≫ ProjectiveSpace.toSpec k 3 = toSpec k := sorry

/-- The coproduct of two projective lines is reducible and admits a closed immersion
into projective three-space over the base field. -/
theorem reducibleWithClosedImmersion (k : Type u) [Field k] :
    ¬ IrreducibleSpace (scheme k) ∧
      ∃ immersion : scheme k ⟶ ProjectiveSpace.scheme k 3,
        IsClosedImmersion immersion ∧
          immersion ≫ ProjectiveSpace.toSpec k 3 = toSpec k := sorry

end AlgebraicGeometry.ProjectiveLine.Coprod
