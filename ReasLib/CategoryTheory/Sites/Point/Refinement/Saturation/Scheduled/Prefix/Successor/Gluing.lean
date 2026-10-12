/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Operations
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Successor.Basic

/-!
# Gluing successor extensions of open scheduled prefixes

This file uses mathlib's `SmallObject.SuccStruct.extendToSucc` in `Under A` to
assemble the explicit based diagram and open prefix at a successor cut.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled.OpenPrefix.SuccExtension

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {M : Type z} [LinearOrder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

variable [SuccOrder (WithTop (WithBot M))]
variable {cut : WithTop (WithBot M)}
variable {D : Stage.Scheduled.OpenPrefix (J := J) A request cut}

/-- The old based diagram regarded as a functor into `Under A`. -/
noncomputable def underFunctor (D : Stage.Scheduled.OpenPrefix (J := J) A request cut) :
    {i : WithTop (WithBot M) // i ≤ cut} ⥤ Under A :=
  Under.lift D.toDiagram.functor D.toDiagram.base

/-- The closed successor-cut functor in `Under A`. -/
noncomputable def toUnderFunctor (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    {i : WithTop (WithBot M) // i ≤ Order.succ cut} ⥤ Under A :=
  SmallObject.SuccStruct.extendToSucc hcut (underFunctor D) extension.underHom

/-- The stage-valued functor underlying a successor extension. -/
noncomputable def toFunctor (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    {i : WithTop (WithBot M) // i ≤ Order.succ cut} ⥤
      Stage.{u, v, q, r, r'} (J := J) S P x y :=
  extension.toUnderFunctor hcut ⋙ Under.forget A

/-- The based stage diagram assembled through the successor cut. -/
noncomputable def toDiagram (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    Stage.Diagram (J := J) A
      {i : WithTop (WithBot M) // i ≤ Order.succ cut} where
  functor := extension.toFunctor hcut
  base := ((Under.forgetCone A).whisker (extension.toUnderFunctor hcut)).π

/-- The canonical comparison from an old stage of the successor diagram to
the corresponding stage of the original prefix. -/
abbrev oldIso (extension : OpenPrefix.SuccExtension D) (hcut : ¬ IsMax cut)
    (i : {i : WithTop (WithBot M) // i ≤ cut}) :
    (extension.toDiagram hcut).stage ⟨i.1, i.2.trans (Order.le_succ cut)⟩ ≅
      D.toDiagram.stage i :=
  (Under.forget A).mapIso
    (SmallObject.SuccStruct.extendToSuccObjIso hcut (underFunctor D)
      extension.underHom i.1 i.2)

/-- The canonical comparison from the new greatest diagram stage to the stage
carried by the successor extension. -/
abbrev succIso (extension : OpenPrefix.SuccExtension D) (hcut : ¬ IsMax cut) :
    (extension.toDiagram hcut).stage ⟨Order.succ cut, le_rfl⟩ ≅ extension.stage :=
  (Under.forget A).mapIso
    (SmallObject.SuccStruct.extendToSuccObjSuccIso hcut (underFunctor D)
      extension.underHom)

/-- The canonical natural isomorphism identifying the restriction of the
successor functor to the old cut with the original prefix functor. -/
abbrev restrictionIso (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    SmallObject.restrictionLE (extension.toFunctor hcut)
      (Order.le_succ cut) ≅ D.toDiagram.functor :=
  Functor.isoWhiskerRight
    (SmallObject.SuccStruct.extendToSuccRestrictionLEIso hcut
      (underFunctor D) extension.underHom)
    (Under.forget A)

namespace toDiagram

/-- The successor diagram satisfies the open-prefix realization invariant. -/
theorem realizes (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    ∀ (i : {j : WithTop (WithBot M) // j ≤ Order.succ cut}) (m : M),
      ((m : WithBot M) : WithTop (WithBot M)) < i.1 →
      (((extension.toDiagram hcut).fromBase i).mapRequest (request m)).is_realized := sorry

end toDiagram

/-- Assemble a successor extension into an explicit open prefix. -/
noncomputable def toPrefix (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    Stage.Scheduled.OpenPrefix (J := J) A request (Order.succ cut) :=
  OpenPrefix.ofDiagram (J := J) (request := request) (extension.toDiagram hcut)
    (toDiagram.realizes extension hcut)

namespace toPrefix

/-- Restricting the explicitly glued successor prefix to the old cut recovers
the original prefix. -/
theorem restrict (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    OpenPrefix.restrict (extension.toPrefix hcut) (Order.le_succ cut) = D := sorry

end toPrefix

end Stage.Scheduled.OpenPrefix.SuccExtension
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
