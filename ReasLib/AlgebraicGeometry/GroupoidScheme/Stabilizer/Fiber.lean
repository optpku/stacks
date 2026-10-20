module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer.RelationAction
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsor.Field
public import ReasLib.AlgebraicGeometry.Scheme.Over.CartesianMonoidal
public import ReasLib.CategoryTheory.Monoidal.Cartesian.Mod.Map

/-!
# Fibres of stabilizer actions

The relation action of a groupoid scheme induces an action of the stabilizer group over the
residue field of each point of the relation base.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.RelationAction

variable {S : Scheme.{u}} (Q : GroupoidScheme S)

/-- The stabilizer group over the residue field at a point of `Q.U ⨯ Q.U`. -/
def fiberGroup (p : (Q.U ⨯ Q.U).left) :
    Grp (Over (Spec ((Q.U ⨯ Q.U).left.residueField p))) :=
  ((Q.U ⨯ Q.U).iteratedSliceEquiv.functor ⋙
      Over.pullback ((Q.U ⨯ Q.U).left.fromSpecResidueField p)).mapGrp.obj (group Q)

/-- The residue-field base change of the stabilizer action on the relation. -/
def fiberAction (p : (Q.U ⨯ Q.U).left) :
    Mod (Over (Spec ((Q.U ⨯ Q.U).left.residueField p))) (fiberGroup Q p).X :=
  CategoryTheory.Functor.mapMod
    ((Q.U ⨯ Q.U).iteratedSliceEquiv.functor ⋙
      Over.pullback ((Q.U ⨯ Q.U).left.fromSpecResidueField p))
    (group Q) (action Q)

/-- The carrier of the residue-field action is the scheme-theoretic fibre of the relation map. -/
theorem fiberAction_X (p : (Q.U ⨯ Q.U).left) :
    (fiberAction Q p).X.left = (Over.Hom.left Q.toPreRelation.hom).fiber p := sorry

/-- The structure morphism of the residue-field action is the canonical map from the fibre to
the spectrum of the residue field. -/
theorem fiberAction_hom (p : (Q.U ⨯ Q.U).left) :
    (fiberAction Q p).X.hom =
      (Over.Hom.left Q.toPreRelation.hom).fiberToSpecResidueField p := sorry

/-- The action on the fibre is the monoidal image of the relation action. -/
theorem fiberAction_smul (p : (Q.U ⨯ Q.U).left) :
    (fiberAction Q p).mod.smul =
      CategoryTheory.Functor.mapModSmul
        ((Q.U ⨯ Q.U).iteratedSliceEquiv.functor ⋙
          Over.pullback ((Q.U ⨯ Q.U).left.fromSpecResidueField p))
        (group Q) (action Q) := sorry

/-- A nonempty scheme-theoretic relation fibre is an fpqc torsor under its fibre stabilizer. -/
theorem fiberAction_isTorsor (p : (Q.U ⨯ Q.U).left)
    (h_nonempty : Nonempty ((Over.Hom.left Q.toPreRelation.hom).fiber p)) :
    GroupScheme.IsTorsor (fiberGroup Q p) (fiberAction Q p) := sorry

end AlgebraicGeometry.GroupoidScheme.RelationAction
