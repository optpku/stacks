module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Operations

/-!
# Computations for closed scheduled saturation prefixes

This file records extensionality, constructor projections, restriction
computations, and the global scheduled-diagram adapter for closed prefixes.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled.Prefix

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

/-- Closed prefixes with the same underlying based diagram are equal. -/
@[ext]
theorem ext {cut : Ω} {D E : Stage.Scheduled.Prefix (J := J) A request cut}
    (h : D.toDiagram = E.toDiagram) :
    D = E := sorry

/-- Forgetting the realization invariant from `ofDiagram D hreal` recovers `D`. -/
@[simp]
theorem ofDiagram.toDiagram {cut : Ω}
    (D : Stage.Diagram (J := J) A {i : Ω // i ≤ cut})
    (hreal : ∀ (m : M) (hm : (m : Ω) ≤ cut),
      ((D.fromBase ⟨(m : Ω), hm⟩).mapRequest (request m)).is_realized) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram = D := sorry

/-- The stage of `ofDiagram D hreal` is the corresponding stage of `D`. -/
@[simp]
theorem ofDiagram.stage {cut : Ω}
    (D : Stage.Diagram (J := J) A {i : Ω // i ≤ cut})
    (hreal : ∀ (m : M) (hm : (m : Ω) ≤ cut),
      ((D.fromBase ⟨(m : Ω), hm⟩).mapRequest (request m)).is_realized)
    (i : {j : Ω // j ≤ cut}) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram.stage i = D.stage i := sorry

/-- A transition of `ofDiagram D hreal` is the corresponding transition of `D`. -/
@[simp]
theorem ofDiagram.hom {cut : Ω}
    (D : Stage.Diagram (J := J) A {i : Ω // i ≤ cut})
    (hreal : ∀ (m : M) (hm : (m : Ω) ≤ cut),
      ((D.fromBase ⟨(m : Ω), hm⟩).mapRequest (request m)).is_realized)
    {i j : {k : Ω // k ≤ cut}} (hij : i ≤ j) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram.hom hij =
      D.hom hij := sorry

/-- A base leg of `ofDiagram D hreal` is the corresponding base leg of `D`. -/
@[simp]
theorem ofDiagram.fromBase {cut : Ω}
    (D : Stage.Diagram (J := J) A {i : Ω // i ≤ cut})
    (hreal : ∀ (m : M) (hm : (m : Ω) ≤ cut),
      ((D.fromBase ⟨(m : Ω), hm⟩).mapRequest (request m)).is_realized)
    (i : {j : Ω // j ≤ cut}) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram.fromBase i =
      D.fromBase i := sorry

/-- The based diagram underlying a constant closed prefix is constant. -/
@[simp]
theorem constant.toDiagram {cut : Ω}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ (m : M) (_ : (m : Ω) ≤ cut),
      (f.mapRequest (request m)).is_realized) :
    (constant (J := J) (request := request) B f hreal).toDiagram =
      Stage.Diagram.constant (J := J) (A := A) (κ := {i : Ω // i ≤ cut}) B f := sorry

/-- Every stage of a constant closed prefix is its chosen target stage. -/
@[simp]
theorem constant.stage {cut : Ω}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ (m : M) (_ : (m : Ω) ≤ cut),
      (f.mapRequest (request m)).is_realized) (i : {j : Ω // j ≤ cut}) :
    (constant (J := J) (request := request) B f hreal).toDiagram.stage i = B := sorry

/-- Every transition of a constant closed prefix is an identity. -/
@[simp]
theorem constant.hom {cut : Ω}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ (m : M) (_ : (m : Ω) ≤ cut),
      (f.mapRequest (request m)).is_realized)
    {i j : {k : Ω // k ≤ cut}} (hij : i ≤ j) :
    (constant (J := J) (request := request) B f hreal).toDiagram.hom hij = 𝟙 B := sorry

/-- Every base leg of a constant closed prefix is its chosen compatible map. -/
@[simp]
theorem constant.fromBase {cut : Ω}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ (m : M) (_ : (m : Ω) ≤ cut),
      (f.mapRequest (request m)).is_realized) (i : {j : Ω // j ≤ cut}) :
    (constant (J := J) (request := request) B f hreal).toDiagram.fromBase i = f := sorry

/-- The based diagram of the bottom prefix is constant at its base stage. -/
@[simp]
theorem bottom.toDiagram
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J) :
    (bottom (J := J) A request).toDiagram =
      Stage.Diagram.constant (J := J) (A := A) (κ := {i : Ω // i ≤ ⊥}) A (𝟙 A) := sorry

/-- Every stage of the bottom prefix is its base stage. -/
@[simp]
theorem bottom.stage
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J) (i : {j : Ω // j ≤ ⊥}) :
    (bottom (J := J) A request).toDiagram.stage i = A := sorry

/-- Every transition of the bottom prefix is the identity of its base stage. -/
@[simp]
theorem bottom.hom
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J) {i j : {k : Ω // k ≤ ⊥}} (hij : i ≤ j) :
    (bottom (J := J) A request).toDiagram.hom hij = 𝟙 A := sorry

/-- Every base leg of the bottom prefix is the identity of its base stage. -/
@[simp]
theorem bottom.fromBase
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J) (i : {j : Ω // j ≤ ⊥}) :
    (bottom (J := J) A request).toDiagram.fromBase i = 𝟙 A := sorry

/-- Restricting a closed-prefix index retains its underlying scheduling node. -/
@[simp]
theorem restrictIndex.apply {cut cut' : Ω} (hcut : cut' ≤ cut)
    (i : {j : Ω // j ≤ cut'}) :
    (restrictIndex hcut i).1 = i.1 := sorry

/-- Restricting a closed prefix evaluates at the same stage of the original diagram. -/
@[simp]
theorem restrictDiagram.stage {cut cut' : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut) (hcut : cut' ≤ cut)
    (i : {j : Ω // j ≤ cut'}) :
    (restrictDiagram D hcut).stage i = D.toDiagram.stage (restrictIndex hcut i) := sorry

/-- Restricting a closed prefix retains the original transition at each comparison. -/
@[simp]
theorem restrictDiagram.hom {cut cut' : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut) (hcut : cut' ≤ cut)
    {i j : {k : Ω // k ≤ cut'}} (hij : i ≤ j) :
    (restrictDiagram D hcut).hom hij =
      D.toDiagram.hom ((restrictIndex hcut).monotone hij) := sorry

/-- Restricting a closed prefix retains its base map at each surviving index. -/
@[simp]
theorem restrictDiagram.fromBase {cut cut' : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut) (hcut : cut' ≤ cut)
    (i : {j : Ω // j ≤ cut'}) :
    (restrictDiagram D hcut).fromBase i =
      D.toDiagram.fromBase (restrictIndex hcut i) := sorry

/-- The underlying diagram of a restricted closed prefix is its restricted diagram. -/
@[simp]
theorem restrict.toDiagram {cut cut' : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut) (hcut : cut' ≤ cut) :
    (restrict D hcut).toDiagram = restrictDiagram D hcut := sorry

/-- Restricting a closed prefix along the identity comparison changes no data. -/
@[simp]
theorem restrict.id {cut : Ω} (D : Stage.Scheduled.Prefix (J := J) A request cut) :
    restrict D (le_rfl : cut ≤ cut) = D := sorry

/-- Successive restrictions agree with restriction along the composite comparison. -/
@[simp]
theorem restrict.comp {cut cut' cut'' : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut) (hcut : cut' ≤ cut)
    (hcut' : cut'' ≤ cut') :
    restrict (restrict D hcut) hcut' = restrict D (le_trans hcut' hcut) := sorry

/-- The full-schedule index embedding retains its scheduling node. -/
@[simp]
theorem scheduledIndex.apply {cut : Ω} (hcut : ∀ i : Ω, i ≤ cut) (i : Ω) :
    (scheduledIndex hcut i).1 = i := sorry

/-- A globally reindexed closed prefix evaluates at the corresponding prefix stage. -/
@[simp]
theorem scheduledStageDiagram.stage {cut : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut) (hcut : ∀ i : Ω, i ≤ cut)
    (i : Ω) :
    (scheduledStageDiagram D hcut).stage i =
      D.toDiagram.stage (scheduledIndex hcut i) := sorry

/-- A global transition is the corresponding transition of the closed prefix. -/
@[simp]
theorem scheduledStageDiagram.hom {cut : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut) (hcut : ∀ i : Ω, i ≤ cut)
    {i j : Ω} (hij : i ≤ j) :
    (scheduledStageDiagram D hcut).hom hij =
      D.toDiagram.hom ((scheduledIndex hcut).monotone hij) := sorry

/-- A global base leg is the corresponding base leg of the closed prefix. -/
@[simp]
theorem scheduledStageDiagram.fromBase {cut : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut) (hcut : ∀ i : Ω, i ≤ cut)
    (i : Ω) :
    (scheduledStageDiagram D hcut).fromBase i =
      D.toDiagram.fromBase (scheduledIndex hcut i) := sorry

/-- Forgetting the schedule invariant from the global adapter recovers the reindexed diagram. -/
@[simp]
theorem toScheduledDiagram.toDiagram {cut : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut) (hcut : ∀ i : Ω, i ≤ cut) :
    (toScheduledDiagram D hcut).toDiagram = scheduledStageDiagram D hcut := sorry

/-- The global adapter evaluates at the corresponding closed-prefix stage. -/
@[simp]
theorem toScheduledDiagram.stage {cut : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut) (hcut : ∀ i : Ω, i ≤ cut)
    (i : Ω) :
    (toScheduledDiagram D hcut).toDiagram.stage i =
      D.toDiagram.stage (scheduledIndex hcut i) := sorry

/-- A transition of the global adapter is the corresponding closed-prefix transition. -/
@[simp]
theorem toScheduledDiagram.hom {cut : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut) (hcut : ∀ i : Ω, i ≤ cut)
    {i j : Ω} (hij : i ≤ j) :
    (toScheduledDiagram D hcut).toDiagram.hom hij =
      D.toDiagram.hom ((scheduledIndex hcut).monotone hij) := sorry

/-- A base leg of the global adapter is the corresponding closed-prefix base leg. -/
@[simp]
theorem toScheduledDiagram.fromBase {cut : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut) (hcut : ∀ i : Ω, i ≤ cut)
    (i : Ω) :
    (toScheduledDiagram D hcut).toDiagram.fromBase i =
      D.toDiagram.fromBase (scheduledIndex hcut i) := sorry

/-- Realization recorded at a scheduled node persists to every later node in the prefix. -/
theorem realizesAt.ofLE {cut : Ω}
    (D : Stage.Scheduled.Prefix (J := J) A request cut)
    {m : M} {i : {k : Ω // k ≤ cut}} (hmi : (m : Ω) ≤ i) :
    ((D.toDiagram.fromBase i).mapRequest (request m)).is_realized := sorry

end Stage.Scheduled.Prefix
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
