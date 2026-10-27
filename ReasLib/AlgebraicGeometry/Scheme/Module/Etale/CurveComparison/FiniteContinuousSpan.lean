/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommInvariants
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.RingTheory.Finiteness.Cardinality

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
    (M.obj.ρ g).hom m ∈ span R G M S := by
  have hle : span R G M S ≤ (span R G M S).comap (M.obj.ρ g).hom := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨h, s⟩, rfl⟩
    change g • (h • s.val) ∈ span R G M S
    rw [← mul_smul]
    exact Submodule.subset_span ⟨(g * h, s), rfl⟩
  exact hle hm

/-- Finite coefficients, compact G and individual open stabilizers make
the invariant span of a finite set FINITE. These hypotheses are explicit. -/
theorem finite [Finite R] [CompactSpace G] (hS : S.Finite) :
    Finite (span R G M S) := by
  have horbit : ∀ s : S, (MulAction.orbit G s.val).Finite := by
    intro s
    letI : Finite (G ⧸ MulAction.stabilizer G s.val) :=
      Subgroup.quotient_finite_of_isOpen _ (M.property s.val)
    letI : Finite (MulAction.orbit G s.val) :=
      Finite.of_equiv (G ⧸ MulAction.stabilizer G s.val)
        (MulAction.orbitEquivQuotientStabilizer G s.val).symm
    exact Set.toFinite _
  have hgen : (Set.range (fun gs : G × S ↦ (M.obj.ρ gs.1).hom gs.2.val)).Finite := by
    have heq : Set.range (fun gs : G × S ↦ (M.obj.ρ gs.1).hom gs.2.val) =
        ⋃ s : S, MulAction.orbit G s.val := by
      ext x
      simp only [Set.mem_range, Set.mem_iUnion, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨⟨g, s⟩, h⟩
        exact ⟨s, g, h⟩
      · rintro ⟨s, g, h⟩
        exact ⟨(g, s), h⟩
    rw [heq]
    letI : Finite S := hS.to_subtype
    exact Set.finite_iUnion horbit
  exact (hgen.submoduleSpan R).to_subtype

/-- Restrict the original action to this specified span. -/
def action : Action (ModuleCat.{max u v} R) G where
  V := ModuleCat.of R (span R G M S)
  ρ := { toFun := fun g ↦ ModuleCat.ofHom
          { toFun := fun m ↦ ⟨(M.obj.ρ g).hom m.val, stable R G M S g m.val m.property⟩
            map_add' := by
              intro x y
              apply Subtype.ext
              exact map_add (M.obj.ρ g).hom x.val y.val
            map_smul' := by
              intro r x
              apply Subtype.ext
              exact map_smul (M.obj.ρ g).hom r x.val }
         map_one' := by
           apply ModuleCat.hom_ext
           apply LinearMap.ext
           intro x
           apply Subtype.ext
           change (1 : G) • x.val = x.val
           exact one_smul G x.val
         map_mul' := by
           intro g h
           apply ModuleCat.hom_ext
           apply LinearMap.ext
           intro x
           apply Subtype.ext
           change (g * h) • x.val = g • (h • x.val)
           exact mul_smul g h x.val }

/-- Subrepresentation vectors retain their original open stabilizers. -/
theorem action_open : openStabilizer R G (action R G M S) := by
  intro m
  have hstab : (MulAction.stabilizer G m : Set G) =
      (MulAction.stabilizer G m.val : Set G) := by
    ext g
    change (g • m = m) ↔ (g • m.val = m.val)
    exact Subtype.ext_iff
  rw [hstab]
  exact M.property m.val

/-- The actual subrepresentation, before any finite-type claim. -/
def obj : DiscreteModuleCat R G := ⟨action R G M S, action_open R G M S⟩

/-- Inclusion is literally subtype inclusion on the original coefficient carrier. -/
def inclusion : obj R G M S ⟶ M :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom (span R G M S).subtype
      comm := fun _ ↦ by rfl }

/-- The specified original vectors belong to their invariant span. -/
theorem mem (s : M.obj.V) (hs : s ∈ S) : s ∈ span R G M S := by
  apply Submodule.subset_span
  exact ⟨(1, ⟨s, hs⟩), one_smul G s⟩

/-- Equivariant maps carry the span into any invariant target containing the
images of the specified generators. Used to define finite subcomplex differentials. -/
theorem span_le_comap {N : DiscreteModuleCat R G} (f : M ⟶ N)
    (T : Submodule R N.obj.V)
    (hT : ∀ g : G, ∀ m ∈ T, (N.obj.ρ g).hom m ∈ T)
    (hS : ∀ s ∈ S, f.hom.hom.hom s ∈ T) :
    span R G M S ≤ T.comap f.hom.hom.hom := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, s⟩, rfl⟩
  change f.hom.hom.hom ((M.obj.ρ g).hom s.val) ∈ T
  have heq := ConcreteCategory.congr_hom (f.hom.comm g) s.val
  change f.hom.hom.hom ((M.obj.ρ g).hom s.val) =
    (N.obj.ρ g).hom (f.hom.hom.hom s.val) at heq
  rw [heq]
  exact hT g _ (hS s.val s.property)

end FiniteContinuousSpan
