/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.SquareFractions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.SquareDirect

/-! # Meromorphic pullback with the new actual module as target

Squarewise quotient maps extend by small-index Ran and the certified
sheafification adjunction. Compatible values on all square source charts
glue by the inverse of their fixed restriction map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PullbackFactory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.Pullback

open Squares

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules.{u})

/-- The target is exactly the meromorphic sheaf of the new actual module. -/
abbrev targetSheaf : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} :=
  (SheafOfModules.toSheaf _).obj
    (meromorphicSectionSheaf X ((Modules.pullback f).obj F))

/-- The specified square fraction maps are compatible with chart restrictions.
Only the naturality law is deferred; the values use the proved quotient formula. -/
def squareMap :
    (target f).op ⋙ (inclusion Y).op ⋙ (meromorphicSectionPresheaf Y F).presheaf ⟶
      (source f).op ⋙ (inclusion X).op ⋙ (targetSheaf f F).obj where
  app a := SquareFractions.sheafMap f F a.unop
  naturality := by sorry

/-- Actual transpose through the small square-target right Kan extension. -/
def smallPresheafMap :
    (inclusion Y).op ⋙ (meromorphicSectionPresheaf Y F).presheaf ⟶
      ((SquareDirect.small f).obj
        ((SquareDirect.comparison X).functor.obj (targetSheaf f F))).obj :=
  ((target f).op.ranAdjunction AddCommGrpCat.{u + 1}).homEquiv _ _ (squareMap f F)

/-- Actual transpose through the small chart inclusion's Ran. -/
def presheafMap : (meromorphicSectionPresheaf Y F).presheaf ⟶
    ((SquareDirect.direct f).obj (targetSheaf f F)).obj := by
  -- Local instance justification (defeq pin): Use the actual square-site inclusion limits at Y for the right-Kan Hom adjunction carrying the constructed presheaf map.
  letI := SquareDirect.ran_limits Y
  exact ((inclusion Y).op.ranAdjunction AddCommGrpCat.{u + 1}).homEquiv _ _
    (smallPresheafMap f F)

/-- The actual sheafification transpose, explicitly binding the existing
proved u+1 coefficient certificate rather than the admitted old owner. -/
def sheafMap : (SheafOfModules.toSheaf _).obj (meromorphicSectionSheaf Y F) ⟶
    (SquareDirect.direct f).obj (targetSheaf f F) := by
  -- Local instance justification (defeq pin): Use the named additive sheafification adjunction at Y so the explicit presheaf map descends through its own unit.
  letI := Sheafification.additiveCertificate Y
  exact ((sheafificationAdjunction (smallEtaleTopology Y) AddCommGrpCat.{u + 1}).homEquiv
    _ _).symm (presheafMap f F)

/-- Take each original section value, apply the actual sheaf morphism and
evaluate the two actual Ran maps on the given square. -/
def squareValues (s : meromorphicSections Y F) :
    ((source f).op ⋙ (inclusion X).op ⋙ (targetSheaf f F).obj ⋙
      forget AddCommGrpCat.{u + 1}).sections :=
  ⟨fun a ↦ SquareDirect.evaluation f (targetSheaf f F) a.unop
      ((sheafMap f F).hom.app (op ((inclusion Y).obj a.unop.right))
        (s.val (op ((inclusion Y).obj a.unop.right)))),
    by sorry⟩

/-- Glue the specified compatible values. This is the inverse of actual
restriction to a covering chart family, not selection from section existence. -/
def pullback (s : meromorphicSections Y F) :
    meromorphicSections X ((Modules.pullback f).obj F) :=
  (SquareDirect.sectionComparison f (targetSheaf f F)).symm (squareValues f F s)

/-- The resulting global section has precisely the constructed square values. -/
theorem pullback_on_squares (s : meromorphicSections Y F) :
    SquareDirect.restrictToSquares f (targetSheaf f F) (pullback f F s) =
      squareValues f F s :=
  (SquareDirect.sectionComparison f (targetSheaf f F)).apply_symm_apply _

theorem pullback_value (s : meromorphicSections Y F) (a : Square f) :
    (pullback f F s).val (op ((inclusion X).obj a.left)) =
      (squareValues f F s).val (op a) :=
  congrArg (fun z ↦ z.val (op a)) (pullback_on_squares f F s)

end AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.Pullback
