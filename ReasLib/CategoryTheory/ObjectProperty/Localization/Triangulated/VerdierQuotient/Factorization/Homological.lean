/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Localization.Lifting.Computation
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.VerdierQuotient.Kernel
public import ReasLib.CategoryTheory.Pretriangulated.Functor.Localization.Lift
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Homological Functors out of Verdier Quotients

The canonical factor is concrete data built by the strict localization construction.  Its
homologicality and the source-facing uniqueness statement are kept as separate Prop-valued API.
-/

open CategoryTheory
open CategoryTheory.ObjectProperty
open scoped CategoryTheory.ObjectProperty

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.VerdierQuotient.Homological

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D]
  [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] (P : ObjectProperty D)
  {A : Type u₂} [Category.{v₂} A] [Abelian A]

/-- Stacks 05RJ: the canonical homological factor through the Verdier quotient, given the
inversion witness required by the localization construction. -/
@[stacks 05RJ "canonical homological Verdier factor"]
noncomputable abbrev factor (H : D ⥤ A) [H.IsHomological]
    (h_inverts : P.trW.IsInvertedBy H) : D / P ⥤ A :=
  Localization.Construction.lift H h_inverts

namespace factor

/-- The canonical comparison from the composite of the quotient functor and the homological
factor to the original functor. -/
@[stacks 05RJ "comparison for the homological Verdier factor"]
noncomputable abbrev facIso (H : D ⥤ A) [H.IsHomological]
    (h_inverts : P.trW.IsInvertedBy H) :
    P.trW.Q ⋙ factor P H h_inverts ≅ H :=
  Localization.Lifting.iso P.trW.Q P.trW H (factor P H h_inverts)

/-- The canonical homological factor strictly composes with the quotient functor to the
original functor. -/
@[simp, stacks 05RJ "strict factorization of the homological Verdier factor"]
theorem fac (H : D ⥤ A) [H.IsHomological]
    (h_inverts : P.trW.IsInvertedBy H) :
    P.trW.Q ⋙ factor P H h_inverts = H := sorry

section

variable [IsTriangulated D] [P.IsTriangulated]

/-- The canonical factor of a homological functor through a Verdier quotient is homological. -/
@[stacks 05RJ "homologicality of the canonical Verdier factor"]
noncomputable instance isHomological (H : D ⥤ A) [H.IsHomological]
    (h_inverts : P.trW.IsInvertedBy H) :
    (factor P H h_inverts).IsHomological := sorry

end

/-- The canonical homological factor maps a morphism from the quotient functor by conjugating
its original image with `facIso`. -/
@[reassoc, stacks 05RJ "map computation for the homological Verdier factor"]
theorem map_Q (H : D ⥤ A) [H.IsHomological]
    (h_inverts : P.trW.IsInvertedBy H) {X Y : D} (f : X ⟶ Y) :
    (factor P H h_inverts).map (P.trW.Q.map f) =
      (facIso P H h_inverts).hom.app X ≫ H.map f ≫
        (facIso P H h_inverts).inv.app Y := sorry

end factor

section

variable [IsTriangulated D] [P.IsTriangulated]

/-- Stacks 05RJ: a homological functor vanishing on `P` has a unique strict homological
factorization through the Verdier quotient by `P`. -/
@[stacks 05RJ]
theorem existsUnique (H : D ⥤ A) [H.IsHomological]
    (hP : P ≤ H.homologicalKernel) :
    ∃! H' : D / P ⥤ A, P.trW.Q ⋙ H' = H ∧ H'.IsHomological := sorry

end

end CategoryTheory.ObjectProperty.VerdierQuotient.Homological
