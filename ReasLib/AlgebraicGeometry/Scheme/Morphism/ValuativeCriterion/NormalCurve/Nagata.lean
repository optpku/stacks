/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.NormalCurve
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyClosed.FinitePresentation

/-!
# The normal-curve valuative criterion over a Nagata base

Universal closedness of a quasi-compact morphism between schemes locally of finite type over a
Nagata base can be tested on finite-dimensional relative affine spaces or on punctured normal
integral curves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.NormalCurvePunctureValuativeCriterion

/-- For a quasi-compact morphism between schemes locally of finite type over a Nagata base,
universal closedness is equivalent to closedness after every finite-dimensional relative
affine-space base change and to existence in every punctured normal-curve valuative test. -/
theorem universallyClosed_tfae {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    [Scheme.Nagata S] [QuasiCompact f] [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (hf_over : f ≫ pY = pX) :
    List.TFAE
      [ UniversallyClosed f
      , ∀ n : ℕ,
          IsClosedMap (pullback.snd f (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y)).base
      , Existence pX pY f
      ] := sorry

/-- A morphism between schemes locally of finite type over a Nagata base is separated if and
only if every punctured normal-curve valuative test has at most one lift. -/
@[stacks 0GWW "Nagata normal-curve valuative criterion for separatedness"]
theorem isSeparated_iff_uniqueness {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (f : X ⟶ Y) [Scheme.Nagata S] [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (hf_over : f ≫ pY = pX) :
    IsSeparated f ↔ Uniqueness pX pY f := sorry

/-- A quasi-compact morphism between schemes locally of finite type over a Nagata base is proper
if and only if every punctured normal-curve valuative test has exactly one lift. -/
@[stacks 0GWX "Nagata normal-curve valuative criterion for properness"]
theorem isProper_iff_existsUnique {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (f : X ⟶ Y) [Scheme.Nagata S] [QuasiCompact f] [LocallyOfFiniteType pX]
    [LocallyOfFiniteType pY] (hf_over : f ≫ pY = pX) :
    IsProper f ↔ ExistsUnique pX pY f := sorry

end AlgebraicGeometry.NormalCurvePunctureValuativeCriterion
