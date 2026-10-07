module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.Basic

/-!
# Computations for arbitrary-cut extensions

This file exposes the cocone, base-factorization, request-transport, and
realization API used by downstream recursive constructions.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled.OpenPrefix.CutExtension

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
variable {D : Stage.Diagram (J := J) A {i : WithTop (WithBot M) // i < cut}}

/-- Extensions are determined by their based cocone. -/
@[ext]
theorem ext {extension extension' : OpenPrefix.CutExtension (request := request) D}
    (hcocone : extension.cocone = extension'.cocone) :
    extension = extension' := sorry

namespace cocone

/-- The named extension stage is the object underlying its based cocone point. -/
@[simp]
theorem stage (extension : OpenPrefix.CutExtension (request := request) D) :
    extension.stage = extension.cocone.pt.right := sorry

/-- The named extension base leg is the structure map of its based cocone point. -/
@[simp]
theorem fromBase (extension : OpenPrefix.CutExtension (request := request) D) :
    extension.fromBase = extension.cocone.pt.hom := sorry

/-- A named predecessor leg underlies the corresponding based cocone map. -/
@[simp]
theorem leg (extension : OpenPrefix.CutExtension (request := request) D)
    (i : {i : WithTop (WithBot M) // i < cut}) :
    extension.leg i = (extension.cocone.ι.app i).right := sorry

end cocone

/-- A diagram transition followed by the later cocone leg is the earlier cocone leg. -/
@[reassoc (attr := simp)]
theorem leg.naturality (extension : OpenPrefix.CutExtension (request := request) D)
    {i j : {k : WithTop (WithBot M) // k < cut}} (hij : i ≤ j) :
    D.hom hij ≫ extension.leg j = extension.leg i := sorry

/-- The extension base leg factors through every strict predecessor. -/
theorem fromBase.fac (extension : OpenPrefix.CutExtension (request := request) D)
    (i : {i : WithTop (WithBot M) // i < cut}) :
    extension.fromBase = D.fromBase i ≫ extension.leg i := sorry

/-- Request transport along a predecessor leg is natural in the predecessor index. -/
theorem leg.mapRequest (extension : OpenPrefix.CutExtension (request := request) D)
    {i j : {k : WithTop (WithBot M) // k < cut}} (hij : i ≤ j)
    (r : (D.stage i).target.Request J) :
    (extension.leg i).mapRequest r =
      (extension.leg j).mapRequest ((D.hom hij).mapRequest r) := sorry

/-- Transporting a base request directly to the extension agrees with transport
through any strict predecessor. -/
theorem fromBase.mapRequest (extension : OpenPrefix.CutExtension (request := request) D)
    (i : {i : WithTop (WithBot M) // i < cut}) (r : A.target.Request J) :
    extension.fromBase.mapRequest r =
      (extension.leg i).mapRequest ((D.fromBase i).mapRequest r) := sorry

/-- The extension realizes every request scheduled strictly before its cut. -/
theorem realizes (extension : OpenPrefix.CutExtension (request := request) D)
    (m : M) (hm : ((m : WithBot M) : WithTop (WithBot M)) < cut) :
    (extension.fromBase.mapRequest (request m)).is_realized := sorry

/-- A request realized at a strict predecessor remains realized at the extension stage. -/
theorem realizes.ofPredecessor
    (extension : OpenPrefix.CutExtension (request := request) D)
    (i : {i : WithTop (WithBot M) // i < cut}) (m : M)
    (hreal : ((D.fromBase i).mapRequest (request m)).is_realized) :
    (extension.fromBase.mapRequest (request m)).is_realized := sorry

/-- Realization after a predecessor transition propagates through the extension leg. -/
theorem realizes.ofHom (extension : OpenPrefix.CutExtension (request := request) D)
    {i j : {k : WithTop (WithBot M) // k < cut}} (hij : i ≤ j)
    {r : (D.stage i).target.Request J}
    (hreal : ((D.hom hij).mapRequest r).is_realized) :
    ((extension.leg i).mapRequest r).is_realized := sorry

namespace constantPrefix

/-- The based diagram underlying an extension's constant-prefix adapter is the
constant diagram at its new stage and base leg. -/
@[simp]
theorem toDiagram (extension : OpenPrefix.CutExtension (request := request) D) :
    extension.constantPrefix.toDiagram =
      OpenPrefix.constantDiagram (J := J) (A := A) (cut := cut)
        extension.stage extension.fromBase := sorry

/-- Every stage of an extension's constant-prefix adapter is its new stage. -/
@[simp]
theorem stage (extension : OpenPrefix.CutExtension (request := request) D)
    (i : {j : WithTop (WithBot M) // j ≤ cut}) :
    extension.constantPrefix.toDiagram.stage i = extension.stage := sorry

/-- Every transition of an extension's constant-prefix adapter is an identity. -/
@[simp]
theorem hom (extension : OpenPrefix.CutExtension (request := request) D)
    {i j : {k : WithTop (WithBot M) // k ≤ cut}} (hij : i ≤ j) :
    extension.constantPrefix.toDiagram.hom hij = 𝟙 extension.stage := sorry

/-- Every base leg of an extension's constant-prefix adapter is the extension's
base leg. -/
@[simp]
theorem fromBase (extension : OpenPrefix.CutExtension (request := request) D)
    (i : {j : WithTop (WithBot M) // j ≤ cut}) :
    extension.constantPrefix.toDiagram.fromBase i = extension.fromBase := sorry

end constantPrefix

variable {D : Stage.Diagram (J := J) A
  {i : WithTop (WithBot M) // i < (⊤ : WithTop (WithBot M))}}

namespace toTerminal

/-- The stage of the terminal adapter is the extension stage. -/
@[simp]
theorem stage (extension : OpenPrefix.CutExtension (request := request) D) :
    extension.toTerminal.stage = extension.stage := sorry

/-- The morphism of the terminal adapter is the extension base leg. -/
@[simp]
theorem hom (extension : OpenPrefix.CutExtension (request := request) D) :
    extension.toTerminal.hom = extension.fromBase := sorry

/-- The terminal adapter retains the extension's realization invariant. -/
theorem realizes
    (extension : OpenPrefix.CutExtension (request := request) D) (m : M) :
    (extension.toTerminal.hom.mapRequest (request m)).is_realized := sorry

end toTerminal

end Stage.Scheduled.OpenPrefix.CutExtension
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
