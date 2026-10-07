module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Operations

/-!
# Computations for open scheduled saturation prefixes

This file records extensionality, constructor projections, restriction
computations, and terminal adapters for open prefixes.
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

/-- Open prefixes with the same underlying based diagram are equal. -/
@[ext]
theorem ext {cut : Cut} {D E : Stage.Scheduled.OpenPrefix (J := J) A request cut}
    (h : D.toDiagram = E.toDiagram) :
    D = E := sorry

/-- Forgetting the realization invariant from `ofDiagram D hreal` recovers `D`. -/
@[simp]
theorem ofDiagram.toDiagram {cut : Cut}
    (D : Stage.Diagram (J := J) A {i : Cut // i ≤ cut})
    (hreal : ∀ (i : {j : Cut // j ≤ cut}) (m : M), ((m : Ω) : Cut) < i.1 →
      ((D.fromBase i).mapRequest (request m)).is_realized) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram = D := sorry

/-- The stage of `ofDiagram D hreal` is the corresponding stage of `D`. -/
@[simp]
theorem ofDiagram.stage {cut : Cut}
    (D : Stage.Diagram (J := J) A {i : Cut // i ≤ cut})
    (hreal : ∀ (i : {j : Cut // j ≤ cut}) (m : M), ((m : Ω) : Cut) < i.1 →
      ((D.fromBase i).mapRequest (request m)).is_realized)
    (i : {j : Cut // j ≤ cut}) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram.stage i = D.stage i := sorry

/-- A transition of `ofDiagram D hreal` is the corresponding transition of `D`. -/
@[simp]
theorem ofDiagram.hom {cut : Cut}
    (D : Stage.Diagram (J := J) A {i : Cut // i ≤ cut})
    (hreal : ∀ (i : {j : Cut // j ≤ cut}) (m : M), ((m : Ω) : Cut) < i.1 →
      ((D.fromBase i).mapRequest (request m)).is_realized)
    {i j : {k : Cut // k ≤ cut}} (hij : i ≤ j) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram.hom hij =
      D.hom hij := sorry

/-- A base leg of `ofDiagram D hreal` is the corresponding base leg of `D`. -/
@[simp]
theorem ofDiagram.fromBase {cut : Cut}
    (D : Stage.Diagram (J := J) A {i : Cut // i ≤ cut})
    (hreal : ∀ (i : {j : Cut // j ≤ cut}) (m : M), ((m : Ω) : Cut) < i.1 →
      ((D.fromBase i).mapRequest (request m)).is_realized)
    (i : {j : Cut // j ≤ cut}) :
    (ofDiagram (J := J) (request := request) D hreal).toDiagram.fromBase i =
      D.fromBase i := sorry

/-- Every stage of a constant open-prefix diagram is its chosen target stage. -/
@[simp]
theorem constantDiagram.stage {cut : Cut}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (i : {j : Cut // j ≤ cut}) :
    (constantDiagram (J := J) (A := A) (cut := cut) B f).stage i = B := sorry

/-- Every transition of a constant open-prefix diagram is an identity. -/
@[simp]
theorem constantDiagram.hom {cut : Cut}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    {i j : {k : Cut // k ≤ cut}} (hij : i ≤ j) :
    (constantDiagram (J := J) (A := A) (cut := cut) B f).hom hij = 𝟙 B := sorry

/-- Every base leg of a constant open-prefix diagram is its chosen compatible map. -/
@[simp]
theorem constantDiagram.fromBase {cut : Cut}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (i : {j : Cut // j ≤ cut}) :
    (constantDiagram (J := J) (A := A) (cut := cut) B f).fromBase i = f := sorry

/-- The based diagram underlying a constant open prefix is its constant diagram. -/
@[simp]
theorem constant.toDiagram {cut : Cut}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ (m : M), ((m : Ω) : Cut) < cut →
      (f.mapRequest (request m)).is_realized) :
    (constant (J := J) (request := request) B f hreal).toDiagram =
      constantDiagram (J := J) (A := A) (cut := cut) B f := sorry

/-- Every stage of a constant open prefix is its chosen target stage. -/
@[simp]
theorem constant.stage {cut : Cut}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ (m : M), ((m : Ω) : Cut) < cut →
      (f.mapRequest (request m)).is_realized) (i : {j : Cut // j ≤ cut}) :
    (constant (J := J) (request := request) B f hreal).toDiagram.stage i = B := sorry

/-- Every transition of a constant open prefix is an identity. -/
@[simp]
theorem constant.hom {cut : Cut}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ (m : M), ((m : Ω) : Cut) < cut →
      (f.mapRequest (request m)).is_realized)
    {i j : {k : Cut // k ≤ cut}} (hij : i ≤ j) :
    (constant (J := J) (request := request) B f hreal).toDiagram.hom hij = 𝟙 B := sorry

/-- Every base leg of a constant open prefix is its chosen compatible map. -/
@[simp]
theorem constant.fromBase {cut : Cut}
    (B : Stage.{u, v, q, r, r'} (J := J) S P x y) (f : A ⟶ B)
    (hreal : ∀ (m : M), ((m : Ω) : Cut) < cut →
      (f.mapRequest (request m)).is_realized) (i : {j : Cut // j ≤ cut}) :
    (constant (J := J) (request := request) B f hreal).toDiagram.fromBase i = f := sorry

/-- Restricting an open-prefix index retains its underlying scheduling node. -/
@[simp]
theorem restrictIndex.apply {cut cut' : Cut} (hcut : cut' ≤ cut)
    (i : {j : Cut // j ≤ cut'}) :
    (restrictIndex hcut i).1 = i.1 := sorry

/-- Restricting an open prefix evaluates at the same stage of the original diagram. -/
@[simp]
theorem restrictDiagram.stage {cut cut' : Cut}
    (D : Stage.Scheduled.OpenPrefix (J := J) A request cut) (hcut : cut' ≤ cut)
    (i : {j : Cut // j ≤ cut'}) :
    (restrictDiagram D hcut).stage i = D.toDiagram.stage (restrictIndex hcut i) := sorry

/-- Restricting an open prefix retains the original transition at each comparison. -/
@[simp]
theorem restrictDiagram.hom {cut cut' : Cut}
    (D : Stage.Scheduled.OpenPrefix (J := J) A request cut) (hcut : cut' ≤ cut)
    {i j : {k : Cut // k ≤ cut'}} (hij : i ≤ j) :
    (restrictDiagram D hcut).hom hij =
      D.toDiagram.hom ((restrictIndex hcut).monotone hij) := sorry

/-- Restricting an open prefix retains its base map at each surviving index. -/
@[simp]
theorem restrictDiagram.fromBase {cut cut' : Cut}
    (D : Stage.Scheduled.OpenPrefix (J := J) A request cut) (hcut : cut' ≤ cut)
    (i : {j : Cut // j ≤ cut'}) :
    (restrictDiagram D hcut).fromBase i =
      D.toDiagram.fromBase (restrictIndex hcut i) := sorry

/-- The underlying diagram of a restricted open prefix is its restricted diagram. -/
@[simp]
theorem restrict.toDiagram {cut cut' : Cut}
    (D : Stage.Scheduled.OpenPrefix (J := J) A request cut) (hcut : cut' ≤ cut) :
    (restrict D hcut).toDiagram = restrictDiagram D hcut := sorry

/-- Restricting an open prefix along the identity comparison changes no data. -/
@[simp]
theorem restrict.id {cut : Cut}
    (D : Stage.Scheduled.OpenPrefix (J := J) A request cut) :
    restrict D (le_rfl : cut ≤ cut) = D := sorry

/-- Successive restrictions agree with restriction along the composite comparison. -/
@[simp]
theorem restrict.comp {cut cut' cut'' : Cut}
    (D : Stage.Scheduled.OpenPrefix (J := J) A request cut) (hcut : cut' ≤ cut)
    (hcut' : cut'' ≤ cut') :
    restrict (restrict D hcut) hcut' = restrict D (le_trans hcut' hcut) := sorry

/-- The stage of the terminal adapter is the adjoined top stage. -/
@[simp]
theorem toTerminal.stage
    (D : Stage.Scheduled.OpenPrefix (J := J) A request (⊤ : Cut)) :
    D.toTerminal.stage = D.toDiagram.stage ⟨⊤, le_rfl⟩ := sorry

/-- The map of the terminal adapter is the base leg at the adjoined top stage. -/
@[simp]
theorem toTerminal.hom
    (D : Stage.Scheduled.OpenPrefix (J := J) A request (⊤ : Cut)) :
    D.toTerminal.hom = D.toDiagram.fromBase ⟨⊤, le_rfl⟩ := sorry

/-- The scheduled diagram obtained from a terminal open prefix is constant at its top stage. -/
@[simp]
theorem toTerminalDiagram.toDiagram
    (D : Stage.Scheduled.OpenPrefix (J := J) A request (⊤ : Cut)) :
    D.toTerminalDiagram.toDiagram =
      Stage.Diagram.constant (J := J) (A := A) (κ := Ω)
        (D.toDiagram.stage ⟨⊤, le_rfl⟩) (D.toDiagram.fromBase ⟨⊤, le_rfl⟩) := sorry

/-- Every stage of the scheduled adapter is the top stage of the open prefix. -/
@[simp]
theorem toTerminalDiagram.stage
    (D : Stage.Scheduled.OpenPrefix (J := J) A request (⊤ : Cut)) (i : Ω) :
    D.toTerminalDiagram.toDiagram.stage i = D.toDiagram.stage ⟨⊤, le_rfl⟩ := sorry

/-- Every transition of the scheduled adapter is the identity of the top stage. -/
@[simp]
theorem toTerminalDiagram.hom
    (D : Stage.Scheduled.OpenPrefix (J := J) A request (⊤ : Cut))
    {i j : Ω} (hij : i ≤ j) :
    D.toTerminalDiagram.toDiagram.hom hij = 𝟙 (D.toDiagram.stage ⟨⊤, le_rfl⟩) := sorry

/-- Every base leg of the scheduled adapter is the open prefix's top base leg. -/
@[simp]
theorem toTerminalDiagram.fromBase
    (D : Stage.Scheduled.OpenPrefix (J := J) A request (⊤ : Cut)) (i : Ω) :
    D.toTerminalDiagram.toDiagram.fromBase i =
      D.toDiagram.fromBase ⟨⊤, le_rfl⟩ := sorry

end Stage.Scheduled.OpenPrefix
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
