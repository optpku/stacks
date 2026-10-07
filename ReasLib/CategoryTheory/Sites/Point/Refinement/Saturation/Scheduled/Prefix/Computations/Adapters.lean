module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Adapters

/-!
# Computations for scheduled-diagram and closed-prefix adapters

The two reindexing directions are inverse when the chosen closed cut bounds
the whole scheduling preorder.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled

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

local notation "Ω" => WithBot M

namespace Diagram

/-- Restricting an index to a prefix retains its underlying scheduling
index. -/
@[simp]
theorem prefixIndex.apply (cut : Ω) (i : {j : Ω // j ≤ cut}) :
    prefixIndex cut i = i.1 := sorry

/-- The restricted prefix diagram evaluates at the corresponding stage of
the global scheduled diagram. -/
@[simp]
theorem prefixDiagram.stage (D : Stage.Scheduled.Diagram (J := J) A request)
    (cut : Ω) (i : {j : Ω // j ≤ cut}) :
    (D.prefixDiagram cut).stage i = D.toDiagram.stage i.1 := sorry

/-- A transition of the restricted prefix diagram is the corresponding
global transition. -/
@[simp]
theorem prefixDiagram.hom (D : Stage.Scheduled.Diagram (J := J) A request)
    (cut : Ω) {i j : {k : Ω // k ≤ cut}} (hij : i ≤ j) :
    (D.prefixDiagram cut).hom hij = D.toDiagram.hom hij := sorry

/-- A base leg of the restricted prefix diagram is the corresponding global
base leg. -/
@[simp]
theorem prefixDiagram.fromBase
    (D : Stage.Scheduled.Diagram (J := J) A request)
    (cut : Ω) (i : {j : Ω // j ≤ cut}) :
    (D.prefixDiagram cut).fromBase i = D.toDiagram.fromBase i.1 := sorry

/-- Forgetting the prefix realization invariant after restriction recovers
the restricted based diagram. -/
@[simp]
theorem toPrefix.toDiagram (D : Stage.Scheduled.Diagram (J := J) A request)
    (cut : Ω) : (D.toPrefix cut).toDiagram = D.prefixDiagram cut := sorry

/-- Restricting a scheduled diagram at a greatest cut and then reindexing it
globally recovers the scheduled diagram. -/
@[simp]
theorem toPrefix.toScheduledDiagram
    (D : Stage.Scheduled.Diagram (J := J) A request)
    (cut : Ω) (hcut : ∀ i : Ω, i ≤ cut) :
    (D.toPrefix cut).toScheduledDiagram hcut = D := sorry

end Diagram

namespace Prefix

/-- Reindexing a greatest closed prefix globally and restricting back to its
original cut recovers the prefix. -/
@[simp]
theorem toScheduledDiagram.toPrefix {cut : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut)
    (hcut : ∀ i : Ω, i ≤ cut) :
    (D.toScheduledDiagram hcut).toPrefix cut = D := sorry

/-- At a greatest cut, closed prefixes and global scheduled diagrams are
canonically equivalent by reindexing. -/
noncomputable def equivDiagram (cut : Ω) (hcut : ∀ i : Ω, i ≤ cut) :
    Stage.Scheduled.Prefix (J := J) A request cut ≃
      Stage.Scheduled.Diagram (J := J) A request where
  toFun := fun D => D.toScheduledDiagram hcut
  invFun := fun D => D.toPrefix cut
  left_inv := toScheduledDiagram.toPrefix (cut := cut) (hcut := hcut)
  right_inv := Diagram.toPrefix.toScheduledDiagram (cut := cut) (hcut := hcut)

end Prefix

end Stage.Scheduled
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
