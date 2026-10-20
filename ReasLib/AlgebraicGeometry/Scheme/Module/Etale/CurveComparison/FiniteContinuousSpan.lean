/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommInvariants
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u v

namespace FiniteContinuousSpan
variable (R : Type u) [Ring R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : DiscreteModuleCat R G) (S : Set M.obj.V)

/-- The actual invariant span of the specified vectors. No finite stage is
chosen from an existence-of-comparison assertion. -/
def span : Submodule R M.obj.V :=
  Submodule.span R (Set.range (fun gs : G × S ↦ (M.obj.ρ gs.1).hom gs.2.val))

/-- Translation permutes the generators of the invariant span. -/
theorem stable (g : G) (m : M.obj.V) (hm : m ∈ span R G M S) :
    (M.obj.ρ g).hom m ∈ span R G M S := by sorry

/-- Finite coefficients, compact G and individual open stabilizers make
the invariant span of a finite set FINITE. These hypotheses are explicit. -/
theorem finite [Finite R] [CompactSpace G] (hS : S.Finite) :
    Finite (span R G M S) := by sorry

/-- Restrict the original action to this specified span. -/
def action : Action (ModuleCat.{max u v} R) G where
  V := ModuleCat.of R (span R G M S)
  ρ := { toFun := fun g ↦ ModuleCat.ofHom
          { toFun := fun m ↦ ⟨(M.obj.ρ g).hom m.val, stable R G M S g m.val m.property⟩
            map_add' := by sorry
            map_smul' := by sorry }
         map_one' := by sorry
         map_mul' := by sorry }

/-- Subrepresentation vectors retain their original open stabilizers. -/
theorem action_open : openStabilizer R G (action R G M S) := by sorry

/-- The actual subrepresentation, before any finite-type claim. -/
def obj : DiscreteModuleCat R G := ⟨action R G M S, action_open R G M S⟩

/-- Inclusion is literally subtype inclusion on the original coefficient carrier. -/
def inclusion : obj R G M S ⟶ M :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom (span R G M S).subtype
      comm := fun _ ↦ by sorry }

/-- The specified original vectors belong to their invariant span. -/
theorem mem (s : M.obj.V) (hs : s ∈ S) : s ∈ span R G M S := by sorry

/-- Equivariant maps carry the span into any invariant target containing the
images of the specified generators. Used to define finite subcomplex differentials. -/
theorem span_le_comap {N : DiscreteModuleCat R G} (f : M ⟶ N)
    (T : Submodule R N.obj.V)
    (hT : ∀ g : G, ∀ m ∈ T, (N.obj.ρ g).hom m ∈ T)
    (hS : ∀ s ∈ S, f.hom.hom.hom s ∈ T) :
    span R G M S ≤ T.comap f.hom.hom.hom := by sorry

end FiniteContinuousSpan
