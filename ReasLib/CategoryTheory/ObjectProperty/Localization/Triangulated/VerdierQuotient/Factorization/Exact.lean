module

public import ReasLib.CategoryTheory.Localization.Lifting.Computation
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Kernel
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exact Functors out of Verdier Quotients

This leaf exposes the canonical strict factor, its shift structure, exactness, and the morphism
computation needed by downstream applications.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty
open scoped CategoryTheory.ObjectProperty

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.VerdierQuotient.Exact

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D]
  [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] (P : ObjectProperty D)
  {E : Type u₂} [Category.{v₂} E] [Limits.HasZeroObject E]
  [HasShift E ℤ] [Preadditive E] [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated E]

/-- Stacks 05RJ: the canonical exact factor through the Verdier quotient, given the inversion
witness required by the localization construction. -/
@[stacks 05RJ "canonical exact Verdier factor"]
noncomputable abbrev factor (F : D ⥤ E) [F.CommShift ℤ] [F.IsTriangulated]
    (h_inverts : P.trW.IsInvertedBy F) : D / P ⥤ E :=
  Localization.Construction.lift F h_inverts

namespace factor

/-- The canonical comparison from the composite of the quotient functor and the exact factor
to the original functor. -/
@[stacks 05RJ "comparison for the exact Verdier factor"]
noncomputable abbrev facIso (F : D ⥤ E) [F.CommShift ℤ] [F.IsTriangulated]
    (h_inverts : P.trW.IsInvertedBy F) :
    P.trW.Q ⋙ factor P F h_inverts ≅ F :=
  Localization.Lifting.iso P.trW.Q P.trW F (factor P F h_inverts)

/-- The canonical exact factor strictly composes with the quotient functor to the original
functor. -/
@[simp, stacks 05RJ "strict factorization of the exact Verdier factor"]
theorem fac (F : D ⥤ E) [F.CommShift ℤ] [F.IsTriangulated]
    (h_inverts : P.trW.IsInvertedBy F) :
    P.trW.Q ⋙ factor P F h_inverts = F := sorry

section

variable [IsTriangulated D] [P.IsTriangulated]

/-- The canonical exact factor carries the shift comparison induced by localization. -/
@[stacks 05RJ "shift structure on the canonical exact Verdier factor"]
noncomputable instance commShift (F : D ⥤ E) [F.CommShift ℤ]
    [F.IsTriangulated] (h_inverts : P.trW.IsInvertedBy F) :
    (factor P F h_inverts).CommShift ℤ :=
  Functor.commShiftOfLocalization P.trW.Q P.trW ℤ F (factor P F h_inverts)

/-- The canonical factor of an exact functor through a Verdier quotient is triangulated. -/
@[stacks 05RJ "exactness of the canonical Verdier factor"]
noncomputable instance isTriangulated (F : D ⥤ E) [F.CommShift ℤ]
    [F.IsTriangulated] (h_inverts : P.trW.IsInvertedBy F) :
    (factor P F h_inverts).IsTriangulated := sorry

/-- The canonical exact factor admits the triangulated structure used in the source-facing
universal property. -/
@[stacks 05RJ "triangulated structure on the canonical exact Verdier factor"]
theorem hasTriangulatedStructure (F : D ⥤ E) [F.CommShift ℤ]
    [F.IsTriangulated] (h_inverts : P.trW.IsInvertedBy F) :
    (factor P F h_inverts).HasTriangulatedStructure := sorry

end

/-- The canonical exact factor maps a morphism from the quotient functor by conjugating its
original image with `facIso`. -/
@[reassoc, stacks 05RJ "map computation for the exact Verdier factor"]
theorem map_Q (F : D ⥤ E) [F.CommShift ℤ] [F.IsTriangulated]
    (h_inverts : P.trW.IsInvertedBy F) {X Y : D} (f : X ⟶ Y) :
    (factor P F h_inverts).map (P.trW.Q.map f) =
      (facIso P F h_inverts).hom.app X ≫ F.map f ≫
        (facIso P F h_inverts).inv.app Y := sorry

end factor

section

variable [IsTriangulated D] [P.IsTriangulated]

/-- Stacks 05RJ: an exact functor vanishing on `P` has a unique strict factorization through
the Verdier quotient by `P`, with triangulated structure. -/
@[stacks 05RJ]
theorem existsUnique (F : D ⥤ E) [F.CommShift ℤ] [F.IsTriangulated]
    (hP : P ≤ F.kernel) :
    ∃! F' : D / P ⥤ E,
      P.trW.Q ⋙ F' = F ∧ F'.HasTriangulatedStructure := sorry

end

end CategoryTheory.ObjectProperty.VerdierQuotient.Exact
