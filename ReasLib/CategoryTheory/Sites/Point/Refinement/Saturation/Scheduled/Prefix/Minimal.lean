module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Basic

/-!
# Minimal open scheduled saturation prefixes

A minimal cut contains no concrete scheduled request strictly below it, so the
constant diagram on the base stage supplies the canonical open prefix.
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

/-- At a minimal cut, the realization obligation of the constant identity
diagram is empty. -/
theorem minRealizes {cut : Cut} (hcut : IsMin cut) :
    ∀ (m : M), ((m : Ω) : Cut) < cut →
      (Stage.Hom.mapRequest (J := J) (𝟙 A) (request m)).is_realized := sorry

/-- The canonical open prefix at a minimal cut is constant at the base stage. -/
noncomputable def ofMin {cut : Cut} (hcut : IsMin cut) :
    Stage.Scheduled.OpenPrefix (J := J) A request cut :=
  constant (J := J) (A := A) (request := request) A (𝟙 A) (minRealizes hcut)

/- The data of `ofMin` are the explicit constant stage and identity map; its
`sorryAx` dependency is confined to proposition-valued coherence fields. -/

end Stage.Scheduled.OpenPrefix
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
