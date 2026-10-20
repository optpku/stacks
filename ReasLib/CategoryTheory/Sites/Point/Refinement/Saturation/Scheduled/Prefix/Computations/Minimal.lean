module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Minimal

/-!
# Computations for minimal open prefixes
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

local notation "Ω" => WithBot M
local notation "Cut" => WithTop Ω

/-- The diagram underlying a minimal open prefix is the constant identity
diagram on the base stage. -/
@[simp]
theorem ofMin.toDiagram {cut : Cut} (hcut : IsMin cut) :
    (ofMin (J := J) (A := A) (request := request) hcut).toDiagram =
      constantDiagram (J := J) (A := A) (cut := cut) A (𝟙 A) := sorry

/-- Every stage of a minimal open prefix is the base stage. -/
@[simp]
theorem ofMin.stage {cut : Cut} (hcut : IsMin cut)
    (i : {j : Cut // j ≤ cut}) :
    (ofMin (J := J) (A := A) (request := request) hcut).toDiagram.stage i = A := sorry

/-- Every transition of a minimal open prefix is the identity. -/
@[simp]
theorem ofMin.hom {cut : Cut} (hcut : IsMin cut)
    {i j : {k : Cut // k ≤ cut}} (hij : i ≤ j) :
    (ofMin (J := J) (A := A) (request := request) hcut).toDiagram.hom hij = 𝟙 A := sorry

/-- Every base leg of a minimal open prefix is the identity of the base
stage. -/
@[simp]
theorem ofMin.fromBase {cut : Cut} (hcut : IsMin cut)
    (i : {j : Cut // j ≤ cut}) :
    (ofMin (J := J) (A := A) (request := request) hcut).toDiagram.fromBase i = 𝟙 A := sorry

end Stage.Scheduled.OpenPrefix
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
