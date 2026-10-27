/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommInvariants
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualCoinvariants

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
noncomputable section
universe u

namespace NoncommResidualInvariants
variable (R G Γ Q : Type u) [Ring R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
variable [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
variable (φ : G →ₜ* Γ) (ψ : Γ →ₜ* Q)
variable (hexact : MonoidHom.range φ.toMonoidHom = MonoidHom.ker ψ.toMonoidHom)
variable (hsurj : Function.Surjective ψ)

/-- Actual geometric invariant vectors inside an arbitrary discrete arithmetic representation. -/
def invariants (M : DiscreteModuleCat R Γ) : Submodule R M.obj.V where
  carrier := {m | ∀ g : G, (M.obj.ρ (φ g)).hom m = m}
  zero_mem' := by intro g; exact map_zero _
  add_mem' := by intro x y hx hy g; simp [map_add, hx g, hy g]
  smul_mem' := by intro r x hx g; simp [map_smul, hx g]

omit [IsTopologicalGroup G] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [IsTopologicalGroup Q] [T2Space Q] in
/-- Arithmetic elements with the same quotient image agree on geometric invariants. -/
theorem translate_eq_of_image_eq
    (hexact : MonoidHom.range φ.toMonoidHom = MonoidHom.ker ψ.toMonoidHom)
    (M : DiscreteModuleCat R Γ)
    (m : invariants R G Γ φ M) {a b : Γ} (h : ψ a = ψ b) :
    (M.obj.ρ a).hom m.val = (M.obj.ρ b).hom m.val := by
  have hker : b⁻¹ * a ∈ MonoidHom.ker ψ.toMonoidHom := by
    change ψ (b⁻¹ * a) = 1
    simp [h]
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hexact.symm ▸ hker)
  have hfixed : (b⁻¹ * a) • m.val = m.val := by
    change (M.obj.ρ (b⁻¹ * a)).hom m.val = m.val
    rw [← hg]
    exact m.property g
  change a • m.val = b • m.val
  calc
    a • m.val = (b * (b⁻¹ * a)) • m.val := by simp
    _ = b • ((b⁻¹ * a) • m.val) := mul_smul _ _ _
    _ = b • m.val := congrArg (fun x : M.obj.V ↦ b • x) hfixed

include hexact in
/-- Normality of the geometric kernel makes its invariants arithmetic-stable. -/
theorem stable (M : DiscreteModuleCat R Γ) (γ : Γ) (m : invariants R G Γ φ M) :
    (M.obj.ρ γ).hom m.val ∈ invariants R G Γ φ M := by
  intro g
  have hφ : ψ (φ g) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← hexact]
    exact ⟨g, rfl⟩
  change (φ g) • (γ • m.val) = γ • m.val
  rw [← mul_smul]
  exact translate_eq_of_image_eq R G Γ Q φ ψ hexact M m (by simp [hφ])

/-- Translate invariant vectors by an actual lift of q. Kernel-triviality
proves the group laws and independence of that lift. -/
def action (M : DiscreteModuleCat R Γ) : Action (ModuleCat.{u} R) Q where
  V := ModuleCat.of R (invariants R G Γ φ M)
  ρ :=
    { toFun := fun q ↦ ModuleCat.ofHom
        { toFun := fun m ↦ ⟨(M.obj.ρ (Function.surjInv hsurj q)).hom m.val,
            stable R G Γ Q φ ψ hexact M (Function.surjInv hsurj q) m⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      map_one' := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        apply Subtype.ext
        change (Function.surjInv hsurj 1) • m.val = m.val
        calc
          (Function.surjInv hsurj 1) • m.val = (1 : Γ) • m.val :=
            translate_eq_of_image_eq R G Γ Q φ ψ hexact M m
              (by simp [Function.surjInv_eq])
          _ = m.val := one_smul Γ m.val
      map_mul' := by
        intro a b
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        apply Subtype.ext
        change (Function.surjInv hsurj (a * b)) • m.val =
          (Function.surjInv hsurj a) • ((Function.surjInv hsurj b) • m.val)
        rw [← mul_smul]
        exact translate_eq_of_image_eq R G Γ Q φ ψ hexact M m
          (by simp [Function.surjInv_eq]) }

/-- The residual stabilizer is open via the continuous quotient map Γ→Q.
There is no unrestricted open-kernel assertion for the whole representation. -/
theorem action_open (M : DiscreteModuleCat R Γ) :
    openStabilizer R Q (action R G Γ Q φ ψ hexact hsurj M) := by
  intro m
  have hquot : Topology.IsQuotientMap (ψ : Γ → Q) :=
    .of_surjective_continuous hsurj ψ.continuous
  apply hquot.isCoinducing.isOpen_preimage.mp
  have hpre : (ψ : Γ → Q) ⁻¹' (MulAction.stabilizer Q m : Set Q) =
      (MulAction.stabilizer Γ m.val : Set Γ) := by
    ext γ
    change ((action R G Γ Q φ ψ hexact hsurj M).ρ (ψ γ)).hom m = m ↔
      (M.obj.ρ γ).hom m.val = m.val
    have htranslate := translate_eq_of_image_eq R G Γ Q φ ψ hexact M m
      (Function.surjInv_eq hsurj (ψ γ))
    constructor
    · show ((action R G Γ Q φ ψ hexact hsurj M).ρ (ψ γ)).hom m = m →
        (M.obj.ρ γ).hom m.val = m.val
      intro h
      exact htranslate.symm.trans
        (congrArg (fun x : invariants R G Γ φ M ↦ x.val) h)
    · show (M.obj.ρ γ).hom m.val = m.val →
        ((action R G Γ Q φ ψ hexact hsurj M).ρ (ψ γ)).hom m = m
      intro h
      exact Subtype.ext (htranslate.trans h)
  rw [hpre]
  exact M.property m.val

def obj (M : DiscreteModuleCat R Γ) : DiscreteModuleCat R Q :=
  ⟨action R G Γ Q φ ψ hexact hsurj M, action_open R G Γ Q φ ψ hexact hsurj M⟩

/-- Restrict the actual equivariant coefficient map to its invariant submodules. -/
def map {M N : DiscreteModuleCat R Γ} (f : M ⟶ N) :
    obj R G Γ Q φ ψ hexact hsurj M ⟶ obj R G Γ Q φ ψ hexact hsurj N :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun m ↦ ⟨f.hom.hom.hom m.val, by
            intro g
            have h := congrArg (fun a ↦ a.hom m.val) (f.hom.comm (φ g))
            exact h.symm.trans (congrArg f.hom.hom.hom (m.property g))⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      comm := fun q ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        apply Subtype.ext
        exact congrArg (fun a ↦ a.hom m.val)
          (f.hom.comm (Function.surjInv hsurj q)) }

/-- Relative invariants are defined on ALL discrete arithmetic modules. -/
def functor : DiscreteModuleCat R Γ ⥤ DiscreteModuleCat R Q where
  obj := obj R G Γ Q φ ψ hexact hsurj
  map := map R G Γ Q φ ψ hexact hsurj
  map_id := by intros; rfl
  map_comp := by intros; rfl

instance functor_additive : (functor R G Γ Q φ ψ hexact hsurj).Additive where
  map_add := by intros; rfl

/-- The higher residual action is derived in the full ambient category. -/
def higher (i : ℕ) := (functor R G Γ Q φ ψ hexact hsurj).rightDerived i

end NoncommResidualInvariants
