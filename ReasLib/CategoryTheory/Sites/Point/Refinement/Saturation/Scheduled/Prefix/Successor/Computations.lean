module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Successor.Gluing

/-!
# Computations for gluing successor extensions

This file exposes the old-stage, successor-stage, transition, base-leg,
restriction, and realization formulas for `SuccExtension.toDiagram` and
`SuccExtension.toPrefix`.
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

namespace underFunctor.obj

/-- The lifted old diagram retains the stage at each old index. -/
@[simp]
theorem right
    (i : {i : WithTop (WithBot M) // i ≤ cut}) :
    ((underFunctor D).obj i).right = D.toDiagram.stage i := sorry

/-- The structure map at an old lifted stage is the corresponding base leg. -/
@[simp]
theorem hom
    (i : {i : WithTop (WithBot M) // i ≤ cut}) :
    ((underFunctor D).obj i).hom = D.toDiagram.fromBase i := sorry

end underFunctor.obj

namespace underHom

/-- Forgetting the based successor morphism gives the supplied stage
transition. -/
@[simp]
theorem right (extension : OpenPrefix.SuccExtension D) :
    extension.underHom.right = extension.hom := sorry

end underHom

namespace toDiagram

/-- The functor of the successor diagram is the explicitly glued stage
functor. -/
@[simp]
theorem functor (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    (extension.toDiagram hcut).functor = extension.toFunctor hcut := sorry

end toDiagram

namespace toDiagram.stage

/-- An old node of the successor diagram has the original stage. -/
@[simp]
theorem old (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut)
    (i : {i : WithTop (WithBot M) // i ≤ cut}) :
    (extension.toDiagram hcut).stage
      ⟨i.1, i.2.trans (Order.le_succ cut)⟩ = D.toDiagram.stage i := sorry

/-- The new greatest node of the successor diagram has the extension stage. -/
@[simp]
theorem succ (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    (extension.toDiagram hcut).stage ⟨Order.succ cut, le_rfl⟩ =
      extension.stage := sorry

end toDiagram.stage

namespace toDiagram.hom

/-- Transitions between old nodes are natural with respect to the canonical
old-stage comparisons. -/
@[reassoc]
theorem old (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut)
    {i k : {i : WithTop (WithBot M) // i ≤ cut}} (hik : i ≤ k) :
    (extension.toDiagram hcut).hom hik ≫ (extension.oldIso hcut k).hom =
      (extension.oldIso hcut i).hom ≫ D.toDiagram.hom hik := sorry

/-- The transition from any old node to the successor is the old transition
to the previous maximum followed by the supplied successor transition, up to
the canonical stage comparisons. -/
@[reassoc]
theorem toSucc (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut)
    (i : {i : WithTop (WithBot M) // i ≤ cut}) :
    (extension.toDiagram hcut).hom
        (i.2.trans (Order.le_succ cut)) ≫ (extension.succIso hcut).hom =
      (extension.oldIso hcut i).hom ≫ D.toDiagram.hom i.2 ≫ extension.hom := sorry

/-- The transition from the old maximum to the successor is the supplied
successor transition, up to the canonical stage comparisons. -/
@[reassoc]
theorem succ (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    (extension.toDiagram hcut).hom (Order.le_succ cut) ≫
        (extension.succIso hcut).hom =
      (extension.oldIso hcut ⟨cut, le_rfl⟩).hom ≫ extension.hom := sorry

end toDiagram.hom

namespace toDiagram.fromBase

/-- At every old node, the successor diagram's base leg is the original base
leg after the canonical stage comparison. -/
@[reassoc]
theorem old (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut)
    (i : {i : WithTop (WithBot M) // i ≤ cut}) :
    (extension.toDiagram hcut).fromBase
        ⟨i.1, i.2.trans (Order.le_succ cut)⟩ ≫
      (extension.oldIso hcut i).hom = D.toDiagram.fromBase i := sorry

/-- At the successor node, the new base leg is the extension base leg after
the canonical stage comparison. -/
@[reassoc]
theorem succ (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    (extension.toDiagram hcut).fromBase ⟨Order.succ cut, le_rfl⟩ ≫
      (extension.succIso hcut).hom = extension.fromBase := sorry

end toDiagram.fromBase

namespace restrictionIso

/-- Each component of the restriction comparison is the corresponding
old-stage comparison. -/
@[simp]
theorem homApp (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut)
    (i : {i : WithTop (WithBot M) // i ≤ cut}) :
    (extension.restrictionIso hcut).hom.app i =
      (extension.oldIso hcut i).hom := sorry

end restrictionIso

namespace toPrefix

/-- Forgetting the glued successor prefix returns its explicitly assembled
based diagram. -/
@[simp]
theorem toDiagram (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    (extension.toPrefix hcut).toDiagram = extension.toDiagram hcut := sorry

end toPrefix

namespace toPrefix.fromBase

/-- At every old node, the glued prefix base leg is the original base leg
after the canonical comparison. -/
@[reassoc]
theorem old (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut)
    (i : {i : WithTop (WithBot M) // i ≤ cut}) :
    (extension.toPrefix hcut).toDiagram.fromBase
        ⟨i.1, i.2.trans (Order.le_succ cut)⟩ ≫
      (extension.oldIso hcut i).hom = D.toDiagram.fromBase i := sorry

/-- At the successor node, the glued prefix base leg is the extension base leg
after the canonical comparison. -/
@[reassoc]
theorem succ (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut) :
    (extension.toPrefix hcut).toDiagram.fromBase
        ⟨Order.succ cut, le_rfl⟩ ≫ (extension.succIso hcut).hom =
      extension.fromBase := sorry

end toPrefix.fromBase

namespace toPrefix

/-- The explicitly glued successor prefix realizes every request required
strictly before each of its nodes. -/
theorem realizesBefore (extension : OpenPrefix.SuccExtension D)
    (hcut : ¬ IsMax cut)
    (i : {j : WithTop (WithBot M) // j ≤ Order.succ cut}) (m : M)
    (hm : ((m : WithBot M) : WithTop (WithBot M)) < i.1) :
    (((extension.toPrefix hcut).toDiagram.fromBase i).mapRequest
      (request m)).is_realized := sorry

end toPrefix

end Stage.Scheduled.OpenPrefix.SuccExtension
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
