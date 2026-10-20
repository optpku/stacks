module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.OpenTower.Operations

/-!
# Reindexing computations for open scheduled saturation towers

The terminal top-prefix representation and the all-cuts tower representation
are inverse, with component computations for their underlying based diagrams.
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
local notation "Cut" => WithTop Ω

namespace OpenTower

/-- Open towers with the same underlying based diagram are equal. -/
@[ext]
theorem ext {T U : OpenTower (J := J) A request}
    (h : T.toDiagram = U.toDiagram) : T = U := sorry

/-- Forgetting the realization invariant from `ofDiagram` recovers its based
diagram. -/
@[simp]
theorem ofDiagram.toDiagram (D : Stage.Diagram (J := J) A Cut)
    (hreal : ∀ (cut : Cut) (m : M), ((m : Ω) : Cut) < cut →
      ((D.fromBase cut).mapRequest (request m)).is_realized) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram = D := sorry

/-- The based diagram underlying a constant open tower is constant. -/
@[simp]
theorem constant.toDiagram
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ m : M, (f.mapRequest (request m)).is_realized) :
    (constant (J := J) (request := request) B f hreal).toDiagram =
      Stage.Diagram.constant (J := J) (A := A) (κ := Cut) B f := sorry

/-- Every stage of a constant open tower is its chosen target stage. -/
@[simp]
theorem constant.stage
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ m : M, (f.mapRequest (request m)).is_realized) (cut : Cut) :
    (constant (J := J) (request := request) B f hreal).toDiagram.stage cut = B := sorry

/-- Every transition of a constant open tower is an identity. -/
@[simp]
theorem constant.hom
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ m : M, (f.mapRequest (request m)).is_realized)
    {cut cut' : Cut} (hcut : cut ≤ cut') :
    (constant (J := J) (request := request) B f hreal).toDiagram.hom hcut = 𝟙 B := sorry

/-- Every base leg of a constant open tower is its chosen compatible map. -/
@[simp]
theorem constant.fromBase
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ m : M, (f.mapRequest (request m)).is_realized) (cut : Cut) :
    (constant (J := J) (request := request) B f hreal).toDiagram.fromBase cut = f := sorry

/-- Forgetting the top-bound proof retains the underlying cut. -/
@[simp]
theorem topIndex.apply (i : {cut : Cut // cut ≤ (⊤ : Cut)}) :
    topIndex i = i.1 := sorry

/-- The top-prefix diagram evaluates at the corresponding tower stage. -/
@[simp]
theorem topPrefixDiagram.stage (T : OpenTower (J := J) A request)
    (i : {cut : Cut // cut ≤ (⊤ : Cut)}) :
    T.topPrefixDiagram.stage i = T.toDiagram.stage i.1 := sorry

/-- A top-prefix transition is the corresponding tower transition. -/
@[simp]
theorem topPrefixDiagram.hom (T : OpenTower (J := J) A request)
    {i j : {cut : Cut // cut ≤ (⊤ : Cut)}} (hij : i ≤ j) :
    T.topPrefixDiagram.hom hij = T.toDiagram.hom hij := sorry

/-- A top-prefix base leg is the corresponding tower base leg. -/
@[simp]
theorem topPrefixDiagram.fromBase (T : OpenTower (J := J) A request)
    (i : {cut : Cut // cut ≤ (⊤ : Cut)}) :
    T.topPrefixDiagram.fromBase i = T.toDiagram.fromBase i.1 := sorry

/-- The diagram underlying the terminal top prefix is the top reindexing of
the tower diagram. -/
@[simp]
theorem toTopPrefix.toDiagram (T : OpenTower (J := J) A request) :
    T.toTopPrefix.toDiagram = T.topPrefixDiagram := sorry

/-- Passing from an open tower to its top prefix and back recovers the tower. -/
@[simp]
theorem toTopPrefix.toTower (T : OpenTower (J := J) A request) :
    T.toTopPrefix.toTower = T := sorry

end OpenTower

namespace OpenPrefix

/-- Embedding a cut into the terminal top prefix retains that cut. -/
@[simp]
theorem towerIndex.val (cut : Cut) : (towerIndex cut).1 = cut := sorry

/-- The tower diagram associated to a terminal prefix evaluates at the
corresponding prefix stage. -/
@[simp]
theorem towerDiagram.stage (D : OpenPrefix (J := J) A request (⊤ : Cut))
    (cut : Cut) : D.towerDiagram.stage cut = D.toDiagram.stage (towerIndex cut) := sorry

/-- A reindexed tower transition is the corresponding terminal-prefix
transition. -/
@[simp]
theorem towerDiagram.hom (D : OpenPrefix (J := J) A request (⊤ : Cut))
    {cut cut' : Cut} (hcut : cut ≤ cut') :
    D.towerDiagram.hom hcut = D.toDiagram.hom hcut := sorry

/-- A reindexed tower base leg is the corresponding terminal-prefix base
leg. -/
@[simp]
theorem towerDiagram.fromBase
    (D : OpenPrefix (J := J) A request (⊤ : Cut)) (cut : Cut) :
    D.towerDiagram.fromBase cut = D.toDiagram.fromBase (towerIndex cut) := sorry

/-- The diagram underlying the tower associated to a terminal prefix is its
all-cuts reindexing. -/
@[simp]
theorem toTower.toDiagram (D : OpenPrefix (J := J) A request (⊤ : Cut)) :
    D.toTower.toDiagram = D.towerDiagram := sorry

/-- Passing from a terminal top prefix to its open tower and back recovers
the prefix. -/
@[simp]
theorem toTower.toTopPrefix (D : OpenPrefix (J := J) A request (⊤ : Cut)) :
    D.toTower.toTopPrefix = D := sorry

end OpenPrefix

namespace OpenTower

/-- Open towers and terminal top prefixes are canonically equivalent by
reindexing. -/
noncomputable def equivTopPrefix :
    OpenTower (J := J) A request ≃ OpenPrefix (J := J) A request (⊤ : Cut) where
  toFun := toTopPrefix
  invFun := OpenPrefix.toTower
  left_inv := toTopPrefix.toTower
  right_inv := OpenPrefix.toTower.toTopPrefix

end OpenTower

end Stage.Scheduled
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
