/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Basic

/-!
# Successor-extension data for open scheduled prefixes

This file owns the exact data needed to append one new greatest stage to an
open scheduled prefix.  It is independent of the gluing construction.
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
variable {M : Type z} [LinearOrder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

variable [SuccOrder (WithTop (WithBot M))]

/-- Data for adjoining one new greatest node to an open prefix.  The new point
and transition live in `Under A`, so compatibility with the old base leg is
part of the categorical morphism rather than a separate coherence field. -/
structure SuccExtension {cut : WithTop (WithBot M)}
    (D : Stage.Scheduled.OpenPrefix (J := J) A request cut) where
  /-- The based stage placed at the new successor maximum. -/
  point : Under A
  /-- The based transition from the old maximum to the new point. -/
  underHom :
    (Under.lift D.toDiagram.functor D.toDiagram.base).obj ⟨cut, le_rfl⟩ ⟶ point
  /-- The new point's base leg realizes every request required below the
  successor cut. -/
  realizesBefore : ∀ (m : M),
    ((m : WithBot M) : WithTop (WithBot M)) < Order.succ cut →
    (Stage.Hom.mapRequest (J := J) point.hom (request m)).is_realized

namespace SuccExtension

variable {cut : WithTop (WithBot M)}
variable {D : Stage.Scheduled.OpenPrefix (J := J) A request cut}

/-- Successor extensions are determined by their new based point and transition;
the realization certificate is proposition-valued. -/
@[ext]
theorem ext {extension extension' : SuccExtension D}
    (hpoint : extension.point = extension'.point)
    (hunderHom : HEq extension.underHom extension'.underHom) :
    extension = extension' := sorry

/-- The new stage carried by a successor extension. -/
abbrev stage (extension : SuccExtension D) :
    Stage.{u, v, q, r, r'} (J := J) S P x y :=
  extension.point.right

/-- The transition from the old maximum to the new stage. -/
abbrev hom (extension : SuccExtension D) :
    D.toDiagram.stage ⟨cut, le_rfl⟩ ⟶ extension.stage :=
  extension.underHom.right

/-- The base leg to the new stage carried by a successor extension. -/
abbrev fromBase (extension : SuccExtension D) : A ⟶ extension.stage :=
  extension.point.hom

/-- Construct a successor extension from an explicit new stage, transition,
and realization invariant.  The compatible based morphism is assembled in
`Under A`. -/
noncomputable def ofHom
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : D.toDiagram.stage ⟨cut, le_rfl⟩ ⟶ B)
    (hreal : ∀ (m : M),
      ((m : WithBot M) : WithTop (WithBot M)) < Order.succ cut →
        (Stage.Hom.mapRequest (J := J)
          (D.toDiagram.fromBase ⟨cut, le_rfl⟩ ≫ f) (request m)).is_realized) :
    SuccExtension D where
  point := Under.mk (D.toDiagram.fromBase ⟨cut, le_rfl⟩ ≫ f)
  underHom := Under.homMk f
  realizesBefore := hreal

/-- The successor-extension base leg is the old maximum leg followed by the
new transition. -/
@[simp, reassoc (attr := simp)]
theorem fromBase.eq (extension : SuccExtension D) :
    extension.fromBase =
      D.toDiagram.fromBase ⟨cut, le_rfl⟩ ≫ extension.hom := sorry

namespace ofHom

/-- `ofHom` retains its explicitly supplied new stage. -/
@[simp]
theorem stage
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : D.toDiagram.stage ⟨cut, le_rfl⟩ ⟶ B)
    (hreal : ∀ (m : M),
      ((m : WithBot M) : WithTop (WithBot M)) < Order.succ cut →
        (Stage.Hom.mapRequest (J := J)
          (D.toDiagram.fromBase ⟨cut, le_rfl⟩ ≫ f) (request m)).is_realized) :
    (ofHom B f hreal).stage = B := sorry

/-- `ofHom` retains its explicitly supplied transition. -/
@[simp]
theorem hom
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : D.toDiagram.stage ⟨cut, le_rfl⟩ ⟶ B)
    (hreal : ∀ (m : M),
      ((m : WithBot M) : WithTop (WithBot M)) < Order.succ cut →
        (Stage.Hom.mapRequest (J := J)
          (D.toDiagram.fromBase ⟨cut, le_rfl⟩ ≫ f) (request m)).is_realized) :
    (ofHom B f hreal).hom = f := sorry

/-- The base leg of `ofHom` is the explicit composite through the old
maximum. -/
@[simp]
theorem fromBase
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (f : D.toDiagram.stage ⟨cut, le_rfl⟩ ⟶ B)
    (hreal : ∀ (m : M),
      ((m : WithBot M) : WithTop (WithBot M)) < Order.succ cut →
        (Stage.Hom.mapRequest (J := J)
          (D.toDiagram.fromBase ⟨cut, le_rfl⟩ ≫ f) (request m)).is_realized) :
    (ofHom B f hreal).fromBase =
      D.toDiagram.fromBase ⟨cut, le_rfl⟩ ≫ f := sorry

end ofHom

/-- Every request required below the successor cut is realized by the
successor-extension base leg. -/
theorem realizes (extension : SuccExtension D) (m : M)
    (hm : ((m : WithBot M) : WithTop (WithBot M)) < Order.succ cut) :
    (Stage.Hom.mapRequest (J := J) extension.fromBase (request m)).is_realized := sorry

end SuccExtension

end Stage.Scheduled.OpenPrefix
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
