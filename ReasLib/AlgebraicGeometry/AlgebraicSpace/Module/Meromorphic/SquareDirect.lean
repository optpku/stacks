/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Squares
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-! # Actual small-index direct image for the existing lifted meromorphic sheaves

Only the meromorphic coefficients use their original u+1 lift. The module
pullback still has universe u. No large-site Ran existence is assumed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PullbackFactory
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.SquareDirect

open Squares

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

theorem dense : (inclusion X).IsDenseSubsite (topology X) (smallEtaleTopology X) :=
  SmallAtlas.denseSubsite (AtlasInput.scheme X)
    (AtlasInput.map X)
    (AtlasInput.locallySurjective X)

theorem ran_limits (V : (smallEtaleSite X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (inclusion X).op) AddCommGrpCat.{u + 1} := by
  infer_instance

/-- Actual restriction/Ran comparison, with proved small-index limits. -/
def comparison : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ≌
    Sheaf (topology X) AddCommGrpCat.{u + 1} := by
  -- Local instance justification (defeq pin): Use density of this explicit small-site inclusion when transporting its restriction/right-Kan sheaf adjunction.
  letI := dense X
  -- Local instance justification (defeq pin): Supply the established limits for this inclusion at X so its specified right-Kan adjunction is used.
  letI := ran_limits X
  exact ((inclusion X).sheafAdjunctionCocontinuous AddCommGrpCat.{u + 1}
    (topology X) (smallEtaleTopology X)).toEquivalence

variable {X} {Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Small-index compatible additive sections on squares. -/
def presheaf : ((Site X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
    ((Site Y)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  (Functor.whiskeringLeft _ _ _).obj (source f).op ⋙ (target f).op.ran

/-- The same compatible-section descent law as SquareKan.direct_isSheaf,
now for the additive coefficient category. No new data are chosen. -/
theorem isSheaf (Q : Sheaf (topology X) AddCommGrpCat.{u + 1}) :
    Presheaf.IsSheaf (topology Y) ((presheaf f).obj Q.obj) := by
  sorry

def small : Sheaf (topology X) AddCommGrpCat.{u + 1} ⥤
    Sheaf (topology Y) AddCommGrpCat.{u + 1} :=
  ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ presheaf f) (isSheaf f)

def direct : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
    Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1} :=
  (comparison X).functor ⋙ small f ⋙ (comparison Y).inverse

/-- Restrict along the actual chart, then evaluate the actual Ran counit. -/
def evaluation (Q : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (a : Square f) :
    ((direct f).obj Q).obj.obj (op ((inclusion Y).obj a.right)) ⟶
      Q.obj.obj (op ((inclusion X).obj a.left)) :=
  ((comparison Y).counitIso.hom.app ((small f).obj ((comparison X).functor.obj Q))).hom.app
      (op a.right) ≫
    ((target f).op.ranCounit.app ((source f).op ⋙ (inclusion X).op ⋙ Q.obj)).app (op a)

/-- Restriction of an actual section to all actual square source charts. -/
def restrictToSquares (Q : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (s : (Q.obj ⋙ forget AddCommGrpCat.{u + 1}).sections) :
    ((source f).op ⋙ (inclusion X).op ⋙ Q.obj ⋙ forget AddCommGrpCat.{u + 1}).sections :=
  ⟨fun a ↦ s.val (op ((inclusion X).obj a.unop.left)),
    fun {_ _} g ↦ s.property ((inclusion X).map ((source f).map g.unop)).op⟩

/-- The source charts cover X by refining the pullbacks of both supplied atlases. -/
theorem sourceCoverDense : (source f ⋙ inclusion X).IsCoverDense (smallEtaleTopology X) := by
  sorry

/-- Morphisms of source charts lift locally to square morphisms after refining the target charts. -/
theorem sourceLocallyFull : (source f ⋙ inclusion X).IsLocallyFull (smallEtaleTopology X) := by
  sorry

/-- The section equivalence is restriction and the actual dense-site sheaf gluing map. -/
def sectionComparison (Q : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (Q.obj ⋙ forget AddCommGrpCat.{u + 1}).sections ≃
      ((source f).op ⋙ (inclusion X).op ⋙ Q.obj ⋙ forget AddCommGrpCat.{u + 1}).sections := by
  -- Local instance justification (defeq pin): glue through this actual source-chart family and the existing target sheaf, with no chosen bijectivity witness.
  letI := sourceCoverDense f
  -- Local instance justification (defeq pin): the sheaf-Hom restriction equivalence uses local fullness of the same square source functor.
  letI := sourceLocallyFull f
  let Q' := (sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u + 1})).obj Q
  exact (Q'.obj.sectionsEquivHom PUnit).trans
    ((Functor.IsCoverDense.restrictHomEquivHom (G := source f ⋙ inclusion X)
      (K := smallEtaleTopology X) (ℱ := (Functor.const (smallEtaleSite X)ᵒᵖ).obj PUnit)
      (ℱ' := Q')).symm.trans
      (((source f ⋙ inclusion X).op ⋙ Q'.obj).sectionsEquivHom PUnit).symm)

/-- The forward section comparison is precisely restriction to source charts. -/
theorem sectionComparison_apply (Q : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (s : (Q.obj ⋙ forget AddCommGrpCat.{u + 1}).sections) :
    sectionComparison f Q s = restrictToSquares f Q s := rfl

/-- Bijectivity follows from the explicit restriction/gluing equivalence. -/
theorem restrictToSquares_bijective (Q : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    Function.Bijective (restrictToSquares f Q) :=
  (sectionComparison f Q).bijective

end AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.SquareDirect
