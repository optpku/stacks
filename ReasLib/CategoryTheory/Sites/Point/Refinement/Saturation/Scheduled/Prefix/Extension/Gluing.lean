module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Limits.Shapes.Preorder.CoconeToIic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Predecessor

/-!
# Gluing arbitrary-cut extensions

This file turns the neutral data of a `CutExtension` into the based diagram on
the corresponding closed initial segment. `Cocone.toIic` adjoins the point of
the extension's canonical cocone in `Under A`; forgetting then recovers both
the stage functor and its canonical base legs.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled.OpenPrefix

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {M : Type z} [Preorder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

variable {cut : WithTop (WithBot M)}
variable {D : Stage.Diagram (J := J) A
  {i : WithTop (WithBot M) // i < cut}}

namespace CutExtension

/-- The closed-cut functor in `Under A` obtained by adjoining the extension
cocone point. -/
noncomputable def underFunctor (extension : CutExtension (request := request) D) :
    {i : WithTop (WithBot M) // i ≤ cut} ⥤ Under A :=
  extension.cocone.toIic

/-- The stage-valued functor underlying the closed-cut extension. -/
noncomputable def toFunctor (extension : CutExtension (request := request) D) :
    {i : WithTop (WithBot M) // i ≤ cut} ⥤
      Stage.{u, v, q, r, r'} (J := J) S P x y :=
  extension.underFunctor ⋙ Under.forget A

/-- The based stage diagram on the closed cut assembled from an arbitrary-cut
extension. -/
noncomputable def toDiagram (extension : CutExtension (request := request) D) :
    Stage.Diagram (J := J) A {i : WithTop (WithBot M) // i ≤ cut} where
  functor := extension.toFunctor
  base := ((Under.forgetCone A).whisker extension.underFunctor).π

/-- The canonical comparison from a glued predecessor stage to the original
strict-predecessor stage. -/
abbrev predecessorIso (extension : CutExtension (request := request) D)
    (i : {i : WithTop (WithBot M) // i < cut}) :
    extension.toDiagram.stage ⟨i.1, i.2.le⟩ ≅ D.stage i :=
  (Under.forget A).mapIso
    (Limits.Cocone.toIic.objIso extension.cocone i.1 i.2)

/-- The canonical comparison from the top stage of the glued diagram to the
stage carried by the extension. -/
abbrev cutIso (extension : CutExtension (request := request) D) :
    extension.toDiagram.stage ⟨cut, le_rfl⟩ ≅ extension.stage :=
  (Under.forget A).mapIso
    (Limits.Cocone.toIic.cutIso extension.cocone)

/-- The canonical natural isomorphism identifying the strict restriction of
the glued functor with the original predecessor functor. -/
abbrev restrictionIso (extension : CutExtension (request := request) D) :
    (Set.iioToIic cut).toFunctor ⋙ extension.toFunctor ≅ D.functor :=
  Functor.isoWhiskerRight
    (Limits.Cocone.toIic.restrictionIso extension.cocone) (Under.forget A)

end CutExtension

namespace CutExtension.toDiagram

/-- The glued closed-cut diagram satisfies the open-prefix realization
invariant when the predecessor diagram does. -/
theorem realizes (extension : CutExtension (request := request) D)
    (hD : PredecessorRealizes (request := request) D) :
    ∀ (i : {j : WithTop (WithBot M) // j ≤ cut}) (m : M),
      ((m : WithBot M) : WithTop (WithBot M)) < i.1 →
      (((extension.toDiagram).fromBase i).mapRequest (request m)).is_realized := sorry

end CutExtension.toDiagram

namespace CutExtension

/-- Glue an arbitrary-cut extension to a realized strict-predecessor diagram,
producing the open prefix through the cut. -/
noncomputable def toPrefix (extension : CutExtension (request := request) D)
    (hD : PredecessorRealizes (request := request) D) :
    OpenPrefix (J := J) A request cut :=
  OpenPrefix.ofDiagram (J := J) (request := request) extension.toDiagram
    (CutExtension.toDiagram.realizes extension hD)

end CutExtension

end Stage.Scheduled.OpenPrefix
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
