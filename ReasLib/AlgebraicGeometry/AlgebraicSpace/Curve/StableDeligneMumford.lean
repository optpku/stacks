/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Curve.StableCurves
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.DeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.DeligneMumford

/-!
# Deligne–Mumford stacks of stable curves

The stable loci are open DM substacks of the stack of curves and admit
representable étale surjective scheme atlases.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The stable locus is an open DM substack of the stack of curves. -/
instance instIsOpenDMSubstack_stable (S : Scheme.{u}) :
    IsOpenDMSubstack (stable S) :=
  sorry

/-- The genus-`g` stable locus is an open DM substack of the stack of curves. -/
instance instIsOpenDMSubstack_stableOfGenus (g : ℕ) (S : Scheme.{u}) :
    IsOpenDMSubstack (stableOfGenus g S) :=
  sorry

/-- Every stable family of curves lies in the Deligne–Mumford locus. -/
theorem stable_le_dm (S : Scheme.{u}) : stable S ≤ dm S :=
  sorry

/-- For `2 ≤ g`, every genus-`g` stable family lies in the Deligne–Mumford locus. -/
theorem stableOfGenus_le_dm (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    stableOfGenus g S ≤ dm S :=
  sorry

/-- The stack of stable curves admits a scheme atlas that is representable by
algebraic spaces, étale, and surjective. -/
theorem exists_etale_surjective_atlas_stable (S : Scheme.{u}) :
    ∃ (U : Over S) (p : Classifying.slice U ⟶ ofObjectProperty (stable S)),
      Classifying.relativelyRepresentableByAlgebraicSpaces p ∧
        CohStack.Hom.has (@AlgebraicSpace.Etale S) p ∧
          Classifying.Surjective p :=
  sorry

/-- For `2 ≤ g`, the stack of genus-`g` stable curves admits a scheme atlas
that is representable by algebraic spaces, étale, and surjective. -/
theorem exists_etale_surjective_atlas_stableOfGenus
    (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}) :
    ∃ (U : Over S)
      (p : Classifying.slice U ⟶ ofObjectProperty (stableOfGenus g S)),
      Classifying.relativelyRepresentableByAlgebraicSpaces p ∧
        CohStack.Hom.has (@AlgebraicSpace.Etale S) p ∧
          Classifying.Surjective p :=
  sorry

/-- For `g ≥ 2`, the stack of stable genus-`g` curves over any scheme is
Deligne–Mumford. -/
instance instDeligneMumfordStack_stableOfGenus
    (g : ℕ) [Nat.AtLeastTwo g] (S : Scheme.{u}) :
    CohStack.DeligneMumfordStack (ofObjectProperty (stableOfGenus g S)) where
  toAlgebraicStack := inferInstance
  existsEtaleSurjectiveAtlas :=
    exists_etale_surjective_atlas_stableOfGenus g Nat.AtLeastTwo.prop S

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
