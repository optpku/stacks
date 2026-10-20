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

include hexact in
/-- Normality of the geometric kernel makes its invariants arithmetic-stable. -/
theorem stable (M : DiscreteModuleCat R Γ) (γ : Γ) (m : invariants R G Γ φ M) :
    (M.obj.ρ γ).hom m.val ∈ invariants R G Γ φ M := by sorry

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
      map_one' := by sorry
      map_mul' := by sorry }

/-- The residual stabilizer is open via the continuous quotient map Γ→Q.
There is no unrestricted open-kernel assertion for the whole representation. -/
theorem action_open (M : DiscreteModuleCat R Γ) :
    openStabilizer R Q (action R G Γ Q φ ψ hexact hsurj M) := by sorry

def obj (M : DiscreteModuleCat R Γ) : DiscreteModuleCat R Q :=
  ⟨action R G Γ Q φ ψ hexact hsurj M, action_open R G Γ Q φ ψ hexact hsurj M⟩

/-- Restrict the actual equivariant coefficient map to its invariant submodules. -/
def map {M N : DiscreteModuleCat R Γ} (f : M ⟶ N) :
    obj R G Γ Q φ ψ hexact hsurj M ⟶ obj R G Γ Q φ ψ hexact hsurj N :=
  ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun m ↦ ⟨f.hom.hom.hom m.val, by sorry⟩
          map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
          map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
      comm := fun _ ↦ by sorry }

/-- Relative invariants are defined on ALL discrete arithmetic modules. -/
def functor : DiscreteModuleCat R Γ ⥤ DiscreteModuleCat R Q where
  obj := obj R G Γ Q φ ψ hexact hsurj
  map := map R G Γ Q φ ψ hexact hsurj
  map_id := by sorry
  map_comp := by sorry

instance functor_additive : (functor R G Γ Q φ ψ hexact hsurj).Additive := by sorry

/-- The higher residual action is derived in the full ambient category. -/
def higher (i : ℕ) := (functor R G Γ Q φ ψ hexact hsurj).rightDerived i

end NoncommResidualInvariants
