module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.Pushforward

/-!
# The projective-bundle formula map on Chow groups

This file defines the finite sum of flat pullbacks followed by powers of the tautological
first-Chern cap and states its bijectivity.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula

/-- The degree of the `i`th pullback-and-Chern-power term in a rank-`q + 1`
projective bundle is the common target degree. -/
theorem formulaTermGrade (k : ℤ) (q : ℕ) (i : Fin (q + 1)) :
    (k + (i : ℕ)) + (q : ℤ) - (i : ℕ) = k + ((q + 1 : ℕ) : ℤ) - 1 := by
  calc
    (k + (i : ℕ)) + (q : ℤ) - (i : ℕ) = k + (q : ℤ) := by
      rw [add_right_comm, add_sub_cancel_right]
    _ = k + ((q + 1 : ℕ) : ℤ) - 1 := by
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, add_sub_cancel_right]

/-- The `i`th summand in the projective-bundle formula, including the canonical
transport to the common target degree. -/
noncomputable def formulaTerm
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [hE : Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (k : ℤ) (i : Fin r) :
    @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k + (i : ℕ)) →+
      totalSpaceChowGroup δ p E r π hπ (k + (r : ℤ) - 1) :=
  match r, i, hE with
  | 0, i, _ => Fin.elim0 i
  | q + 1, i, _ =>
      (reindex δ p E (q + 1) π hπ (formulaTermGrade k q i)).toAddMonoidHom.comp
        (pullbackThenC1PowerCap δ p E q π hπ (k + (i : ℕ)) (i : ℕ))

/-- Evaluating a positive-rank projective-bundle formula term gives pullback,
the indicated Chern-power cap, and the common-degree transport. -/
theorem formulaTerm_apply
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (q : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank (q + 1) E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)
    (k : ℤ) (i : Fin (q + 1))
    (α : @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
      (p.relativeDimensionFunction δ) inferInstance (k + (i : ℕ))) :
    formulaTerm δ p E (q + 1) π hπ k i α =
      reindex δ p E (q + 1) π hπ (formulaTermGrade k q i)
        (pullbackThenC1PowerCap δ p E q π hπ (k + (i : ℕ)) (i : ℕ) α) := sorry

/-- The additive map in the projective-bundle formula, obtained by summing its
pullback-and-Chern-power components. -/
noncomputable def formulaMap
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ) :
    ((i : Fin r) →
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k + (i : ℕ))) →+
      totalSpaceChowGroup δ p E r π hπ (k + (r : ℤ) - 1) :=
  ∑ i : Fin r, (formulaTerm δ p E r π hπ k i).comp
    (Pi.evalAddMonoidHom
      (fun j : Fin r ↦ @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k + (j : ℕ))) i)

/-- The projective-bundle formula map evaluates as the finite sum of its
component maps. -/
theorem formulaMap_apply
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ)
    (α : (i : Fin r) →
      @ChowGroup X (LocallyOfFiniteType.isLocallyNoetherian p)
        (p.relativeDimensionFunction δ) inferInstance (k + (i : ℕ))) :
    formulaMap δ p E r π hπ k α =
      ∑ i : Fin r, formulaTerm δ p E r π hπ k i (α i) := sorry

/-- The projective-bundle formula map is bijective in every Chow degree. -/
theorem formulaMap_bijective
    {S X P : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (p : X ⟶ S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
    (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E) (k : ℤ) :
    Function.Bijective (formulaMap δ p E r π hπ k) := sorry

end AlgebraicGeometry.ChowGroup.ProjectiveBundle.Formula
