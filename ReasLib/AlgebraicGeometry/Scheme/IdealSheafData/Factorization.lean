module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Factorization through closed subschemes

The primary lift is constructed from ideal containment. Range containment is
a recognition theorem for reduced sources.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The canonical lift of a scheme morphism through the closed subscheme defined by `Z`. -/
@[stacks 0356 "closed-subscheme lift"]
noncomputable def lift
    {X Y : Scheme.{u}} (Z : X.IdealSheafData) (f : Y ⟶ X) (hZ : Z ≤ f.ker) :
    Y ⟶ Z.subscheme :=
  IsClosedImmersion.lift Z.subschemeι f (Z.ker_subschemeι.le.trans hZ)

/-- The canonical lift followed by the closed-subscheme inclusion is the original morphism. -/
@[reassoc (attr := simp), stacks 0356 "closed-subscheme lift factorization"]
theorem lift_subschemeι
    {X Y : Scheme.{u}} (Z : X.IdealSheafData) (f : Y ⟶ X) (hZ : Z ≤ f.ker) :
    Z.lift f hZ ≫ Z.subschemeι = f := sorry

/-- A lift through a closed subscheme is uniquely determined by its composite with the
inclusion. -/
@[stacks 0356 "closed-subscheme lift uniqueness"]
theorem lift_unique
    {X Y : Scheme.{u}} (Z : X.IdealSheafData) (f : Y ⟶ X) (hZ : Z ≤ f.ker)
    (g : Y ⟶ Z.subscheme) (hg : g ≫ Z.subschemeι = f) :
    g = Z.lift f hZ := sorry

/-- A morphism factors through a closed subscheme exactly when the defining ideal is contained
in its kernel ideal. -/
@[stacks 0356 "closed-subscheme factorization criterion"]
theorem exists_lift_iff_le_ker
    {X Y : Scheme.{u}} (Z : X.IdealSheafData) (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z.subscheme, g ≫ Z.subschemeι = f) ↔ Z ≤ f.ker := sorry

/-- The factorization through a closed subscheme is uniquely determined exactly under the same
ideal-containment criterion. -/
@[stacks 0356 "unique closed-subscheme factorization criterion"]
theorem existsUnique_lift_iff_le_ker
    {X Y : Scheme.{u}} (Z : X.IdealSheafData) (f : Y ⟶ X) :
    (∃! g : Y ⟶ Z.subscheme, g ≫ Z.subschemeι = f) ↔ Z ≤ f.ker := sorry

/-- For a reduced source, ideal containment is equivalent to containment of the set-theoretic
range in the closed support. -/
@[stacks 0356 "closed-subscheme range criterion"]
theorem le_ker_iff_range_subset
    {X Y : Scheme.{u}} [IsReduced Y] (Z : X.IdealSheafData) (f : Y ⟶ X) :
    Z ≤ f.ker ↔ Set.range f ≤ (Z.support : Set X) := sorry

/-- For a reduced source, factorization through the closed subscheme defined by `Z` is detected
by containment of the morphism range in the support of `Z`. -/
@[stacks 0356 "closed-subscheme range factorization criterion"]
theorem exists_lift_iff_range_subset
    {X Y : Scheme.{u}} [IsReduced Y] (Z : X.IdealSheafData) (f : Y ⟶ X) :
    (∃ g : Y ⟶ Z.subscheme, g ≫ Z.subschemeι = f) ↔
      Set.range f ≤ (Z.support : Set X) := sorry

/-- The reduced-source range criterion also exposes uniqueness of the closed-subscheme lift. -/
@[stacks 0356 "unique closed-subscheme range factorization criterion"]
theorem existsUnique_lift_iff_range_subset
    {X Y : Scheme.{u}} [IsReduced Y] (Z : X.IdealSheafData) (f : Y ⟶ X) :
    (∃! g : Y ⟶ Z.subscheme, g ≫ Z.subschemeι = f) ↔
      Set.range f ≤ (Z.support : Set X) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
