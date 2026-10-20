module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.GeometricPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Pullback

/-! # Actual module sections on the small étale squares

The geometric generator comes from the concrete Lan and sheafification
units. The scalar step is the already constructed tensor/sheafification
unit. Neither step uses the old chosen module-pullback adjunction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PullbackFactory Opposite
open Sheaf.InternalModule

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.SquareModule

open Squares

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- An actual section on the Y-vertex gives the colimit/sheafification
generator on the X-vertex; the final map is the dense-site counit inverse. -/
def typeGenerator (Q : Sheaf (smallEtaleTopology Y) (Type u)) (a : Square f) :
    Q.obj.obj (op ((inclusion Y).obj a.right)) ⟶
      ((Geometric.inverse f).obj Q).obj.obj
        (op ((inclusion X).obj a.left)) :=
  SquareKan.squareGenerator f ((inclusion Y).op ⋙ Q.obj) a ≫
    (toSheafify (topology X)
      ((SquareKan.inversePresheaf f).obj ((inclusion Y).op ⋙ Q.obj))).app (op a.left) ≫
    ((TypeComparison.comparison X).counitIso.inv.app
      ((SquareKan.inverse f).obj
        ((TypeComparison.comparison Y).functor.obj Q))).hom.app (op a.left)

/-- The concrete geometric inverse-image module before coefficient extension. -/
abbrev geometricModule (F : Y.Modules.{u}) :=
  (Ringed.topos f).moduleInverseImage (structureSheaf Y) |>.obj F

/-- The same generator transported through the canonical internal-module
forgetful comparison, then through the explicit scalar-extension unit. -/
def sectionValue (F : Y.Modules.{u}) (a : Square f) :
    F.val.obj (op ((inclusion Y).obj a.right)) →
      ((Modules.pullback f).obj F).val.obj
        (op ((inclusion X).obj a.left)) := fun m ↦
  let F' := (Modules.pullback f).obj F
  let Q := (ToInternal.underlying (structureSheaf X)).obj F'
  (EtaleTopos.extensionEvaluation X Q (EtaleTopos.squareArrow f a.geometric))
    ((((ToInternal.underlying (structureSheaf Y)).map
        ((Modules.pullbackPushforwardAdjunction f).unit.app F) ≫
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).hom.app F').hom.app
        (op ((inclusion Y).obj a.right))) m)

/-- Preserve the original meromorphic module's universe lift, and nothing else. -/
def liftedSection (F : Y.Modules.{u}) (a : Square f) :
    (Modules.liftModule F).val.obj (op ((inclusion Y).obj a.right)) →
      (Modules.liftModule ((Modules.pullback f).obj F)).val.obj
        (op ((inclusion X).obj a.left)) :=
  fun m ↦ ULift.up (sectionValue f F a m.down)

/-- The denominator map is the original scheme pullback, now on a small square. -/
abbrev coefficient (a : Square f) :
    (commStructureSheafLift Y).obj.obj (op ((inclusion Y).obj a.right)) ⟶
      (commStructureSheafLift X).obj.obj (op ((inclusion X).obj a.left)) :=
  pullbackStructureSection a.geometric

/-- Actual module pullback is semilinear for the actual coefficient map.
This follows on geometric generators from presheafFunctions_on_square,
and on the scalar step from the proved tensor unit formula. -/
theorem liftedSection_smul (F : Y.Modules.{u}) (a : Square f)
    (r : (commStructureSheafLift Y).obj.obj (op ((inclusion Y).obj a.right)))
    (m : (Modules.liftModule F).val.obj (op ((inclusion Y).obj a.right))) :
    liftedSection f F a (r • m) = (coefficient f a).hom r • liftedSection f F a m := by
  sorry

theorem liftedSection_zero (F : Y.Modules.{u}) (a : Square f) :
    liftedSection f F a 0 = 0 := by sorry

theorem liftedSection_add (F : Y.Modules.{u}) (a : Square f)
    (m n : (Modules.liftModule F).val.obj (op ((inclusion Y).obj a.right))) :
    liftedSection f F a (m + n) = liftedSection f F a m + liftedSection f F a n := by sorry

@[simp]
theorem liftedSection_apply (F : Y.Modules.{u}) (a : Square f)
    (m : (Modules.liftModule F).val.obj (op ((inclusion Y).obj a.right))) :
    liftedSection f F a m = ULift.up (sectionValue f F a m.down) := rfl

end AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.SquareModule
