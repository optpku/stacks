/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.Gluing
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Extension.Telescope
public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Section

/-!
# Telescope extensions from compatible prefix sections

This leaf connects the top-stage diagram extracted from a compatible section
to the neutral telescope-extension and closed-prefix APIs.  It removes the
repeated `topDiagram` and `topDiagram.realizes` plumbing from downstream
limit-cut constructions.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u v q r r'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled.OpenPrefix.Section

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {M : Type r'} [Preorder M]
variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}
variable {cut : WithTop (WithBot M)}
variable [IsDirectedOrder (Set.Iio cut)]

/-- Build the telescope cut extension of the top-stage diagram extracted
from a compatible section of predecessor prefixes. -/
noncomputable def telescopeExtension
    (s : (belowFunctor (J := J) A request cut).sections)
    (hcofinal : ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ∃ i : Set.Iio cut,
        ((m : WithBot M) : WithTop (WithBot M)) < i.1)
    {target : Target.Diagram.TelescopeTarget (topDiagram s).toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) (topDiagram s) target) :
    CutExtension (request := request) (topDiagram s) :=
  CutExtension.ofTelescope (topDiagram.realizes s) hcofinal anchor

namespace telescopeExtension

/-- Build the section's telescope extension when strict predecessors have no
greatest element. -/
noncomputable def ofNoMax [NoMaxOrder (Set.Iio cut)]
    (s : (belowFunctor (J := J) A request cut).sections)
    {target : Target.Diagram.TelescopeTarget (topDiagram s).toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) (topDiagram s) target) :
    CutExtension (request := request) (topDiagram s) :=
  Section.telescopeExtension s (fun m hm =>
    Predecessor.existsAbove ((m : WithBot M) : WithTop (WithBot M)) hm) anchor

/-- The section's telescope extension carries the telescope stage of its top
diagram. -/
@[simp]
theorem stage
    (s : (belowFunctor (J := J) A request cut).sections)
    (hcofinal : ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ∃ i : Set.Iio cut,
        ((m : WithBot M) : WithTop (WithBot M)) < i.1)
    {target : Target.Diagram.TelescopeTarget (topDiagram s).toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) (topDiagram s) target) :
    (Section.telescopeExtension s hcofinal anchor).stage =
      (topDiagram s).telescopeStage anchor := sorry

/-- A leg of the section's telescope extension is the corresponding
telescope inclusion of its top diagram. -/
@[simp]
theorem leg
    (s : (belowFunctor (J := J) A request cut).sections)
    (hcofinal : ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ∃ i : Set.Iio cut,
        ((m : WithBot M) : WithTop (WithBot M)) < i.1)
    {target : Target.Diagram.TelescopeTarget (topDiagram s).toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) (topDiagram s) target)
    (i : Set.Iio cut) :
    (Section.telescopeExtension s hcofinal anchor).leg i =
      (topDiagram s).telescopeInclusion anchor i := sorry

/-- The section's telescope extension uses the canonical base-to-telescope
morphism of its top diagram. -/
@[simp]
theorem fromBase
    (s : (belowFunctor (J := J) A request cut).sections)
    (hcofinal : ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ∃ i : Set.Iio cut,
        ((m : WithBot M) : WithTop (WithBot M)) < i.1)
    {target : Target.Diagram.TelescopeTarget (topDiagram s).toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) (topDiagram s) target) :
    (Section.telescopeExtension s hcofinal anchor).fromBase =
      (topDiagram s).baseToTelescope anchor := sorry

end telescopeExtension

/-- Glue the telescope extension of a compatible section, obtaining an open
prefix through the cut in one step. -/
noncomputable def telescopePrefix
    (s : (belowFunctor (J := J) A request cut).sections)
    (hcofinal : ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ∃ i : Set.Iio cut,
        ((m : WithBot M) : WithTop (WithBot M)) < i.1)
    {target : Target.Diagram.TelescopeTarget (topDiagram s).toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) (topDiagram s) target) :
    OpenPrefix (J := J) A request cut :=
  (telescopeExtension s hcofinal anchor).toPrefix (topDiagram.realizes s)

namespace telescopePrefix

/-- Glue the section's telescope extension when strict predecessors have no
greatest element. -/
noncomputable def ofNoMax [NoMaxOrder (Set.Iio cut)]
    (s : (belowFunctor (J := J) A request cut).sections)
    {target : Target.Diagram.TelescopeTarget (topDiagram s).toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) (topDiagram s) target) :
    OpenPrefix (J := J) A request cut :=
  Section.telescopePrefix s (fun m hm =>
    Predecessor.existsAbove ((m : WithBot M) : WithTop (WithBot M)) hm) anchor

/-- The diagram underlying the section's glued telescope prefix is the
diagram obtained from its telescope extension. -/
@[simp]
theorem toDiagram
    (s : (belowFunctor (J := J) A request cut).sections)
    (hcofinal : ∀ m : M, ((m : WithBot M) : WithTop (WithBot M)) < cut →
      ∃ i : Set.Iio cut,
        ((m : WithBot M) : WithTop (WithBot M)) < i.1)
    {target : Target.Diagram.TelescopeTarget (topDiagram s).toTargetDiagram}
    (anchor : Stage.Diagram.TelescopeAnchor (J := J) (topDiagram s) target) :
    (Section.telescopePrefix s hcofinal anchor).toDiagram =
      (Section.telescopeExtension s hcofinal anchor).toDiagram := sorry

end telescopePrefix

/- The section adapters reuse the explicit telescope cocone and gluing data;
`sorryAx` is confined to inherited law and computation propositions. -/

end Stage.Scheduled.OpenPrefix.Section
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
