/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.Gluing

/-!
# Computations for gluing arbitrary-cut extensions

This file exposes the predecessor, cut, transition, base-leg, restriction, and
realization formulas for `CutExtension.toDiagram` and `CutExtension.toPrefix`.
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
variable {D : Stage.Diagram (J := J) A
  {i : WithTop (WithBot M) // i < cut}}

namespace toDiagram

/-- The functor of the glued based diagram is the closed-cut stage functor. -/
@[simp]
theorem functor (extension : OpenPrefix.CutExtension (request := request) D) :
    extension.toDiagram.functor = extension.toFunctor := sorry

/-- A glued stage below the cut is the corresponding predecessor stage. -/
@[simp]
theorem stageLt
    (extension : OpenPrefix.CutExtension (request := request) D)
    (i : {i : WithTop (WithBot M) // i < cut}) :
    extension.toDiagram.stage ⟨i.1, i.2.le⟩ = D.stage i := sorry

/-- The glued stage at the cut is the extension stage. -/
@[simp]
theorem stageCut
    (extension : OpenPrefix.CutExtension (request := request) D) :
    extension.toDiagram.stage ⟨cut, le_rfl⟩ = extension.stage := sorry

/-- Below the cut, glued transitions are natural with respect to the
predecessor-stage comparisons. -/
@[reassoc]
theorem homLt
    (extension : OpenPrefix.CutExtension (request := request) D)
    {i k : {i : WithTop (WithBot M) // i < cut}} (hik : i ≤ k) :
    extension.toDiagram.hom hik ≫ (extension.predecessorIso k).hom =
      (extension.predecessorIso i).hom ≫ D.hom hik := sorry

/-- The transition from a strict predecessor to the cut is the extension leg,
up to the canonical stage comparisons. -/
@[reassoc]
theorem homToCut
    (extension : OpenPrefix.CutExtension (request := request) D)
    (i : {i : WithTop (WithBot M) // i < cut}) :
    extension.toDiagram.hom i.2.le ≫ extension.cutIso.hom =
      (extension.predecessorIso i).hom ≫ extension.leg i := sorry

/-- The glued base leg below the cut agrees with the predecessor base leg
after the canonical stage comparison. -/
@[reassoc]
theorem fromBaseLt
    (extension : OpenPrefix.CutExtension (request := request) D)
    (i : {i : WithTop (WithBot M) // i < cut}) :
    extension.toDiagram.fromBase ⟨i.1, i.2.le⟩ ≫
      (extension.predecessorIso i).hom = D.fromBase i := sorry

/-- The glued base leg at the cut agrees with the extension base leg after the
canonical stage comparison. -/
@[reassoc]
theorem fromBaseCut
    (extension : OpenPrefix.CutExtension (request := request) D) :
    extension.toDiagram.fromBase ⟨cut, le_rfl⟩ ≫ extension.cutIso.hom =
      extension.fromBase := sorry

end toDiagram

namespace restrictionIso

/-- The strict-restriction comparison has the predecessor-stage comparison as
each component. -/
@[simp]
theorem homApp
    (extension : OpenPrefix.CutExtension (request := request) D)
    (i : {i : WithTop (WithBot M) // i < cut}) :
    extension.restrictionIso.hom.app i = (extension.predecessorIso i).hom := sorry

end restrictionIso

namespace toPrefix

/-- Forgetting the glued prefix returns the explicitly glued based diagram. -/
@[simp]
theorem toDiagram
    (extension : OpenPrefix.CutExtension (request := request) D)
    (hD : OpenPrefix.PredecessorRealizes (request := request) D) :
    (extension.toPrefix hD).toDiagram = extension.toDiagram := sorry

/-- The prefix base leg below the cut agrees with the predecessor base leg
after the canonical stage comparison. -/
@[reassoc]
theorem fromBaseLt
    (extension : OpenPrefix.CutExtension (request := request) D)
    (hD : OpenPrefix.PredecessorRealizes (request := request) D)
    (i : {i : WithTop (WithBot M) // i < cut}) :
    (extension.toPrefix hD).toDiagram.fromBase ⟨i.1, i.2.le⟩ ≫
      (extension.predecessorIso i).hom = D.fromBase i := sorry

/-- The prefix base leg at the cut agrees with the extension base leg after
the canonical stage comparison. -/
@[reassoc]
theorem fromBaseCut
    (extension : OpenPrefix.CutExtension (request := request) D)
    (hD : OpenPrefix.PredecessorRealizes (request := request) D) :
    (extension.toPrefix hD).toDiagram.fromBase ⟨cut, le_rfl⟩ ≫
      extension.cutIso.hom = extension.fromBase := sorry

/-- The glued prefix realizes every request strictly before each of its
indices. -/
theorem realizesBefore
    (extension : OpenPrefix.CutExtension (request := request) D)
    (hD : OpenPrefix.PredecessorRealizes (request := request) D)
    (i : {j : WithTop (WithBot M) // j ≤ cut}) (m : M)
    (hm : ((m : WithBot M) : WithTop (WithBot M)) < i.1) :
    (((extension.toPrefix hD).toDiagram.fromBase i).mapRequest
      (request m)).is_realized := sorry

end toPrefix

end Stage.Scheduled.OpenPrefix.CutExtension
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
