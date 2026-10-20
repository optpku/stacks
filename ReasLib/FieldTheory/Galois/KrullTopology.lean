module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open scoped Topology
open AlgEquiv Filter

universe u v w

namespace FieldExtension

section

variable {F : Type u} {E : Type v}
variable [Field F] [Field E] [Algebra F E] [Algebra.IsIntegral F E]
variable [TopologicalSpace E] [DiscreteTopology E]

/-- The Krull-topological Galois action on an integral extension is continuous when the extension
field has the discrete topology. -/
instance continuousSMulGalOfIsIntegral : ContinuousSMul Gal(E / F) E :=
  (continuousSMul_iff_stabilizer_isOpen).2 stabilizer_isOpen_of_isIntegral

end

section

variable {F : Type u} {E : Type v} {X : Type w}
variable [Field F] [Field E] [Algebra F E]
variable [TopologicalSpace E] [DiscreteTopology E]
variable [TopologicalSpace X]

/-- Continuity of all evaluations `x ↦ g x • y` implies continuity of a map into a
Krull-topological Galois group. -/
theorem continuousOfContinuousGaloisEval
    (g : X → Gal(E/F))
    (hg_eval : ∀ y : E, Continuous fun x ↦ g x • y) :
    Continuous g := by
  rw [continuous_iff_continuousAt]
  intro x₀
  let δ : X → Gal(E/F) := fun x ↦ (g x₀)⁻¹ * g x
  have hmul : Tendsto δ (𝓝 x₀) (𝓝 (1 : Gal(E/F))) := by
    rw [tendsto_def]
    intro U hU
    rcases (krullTopology_mem_nhds_one_iff F E U).1 hU with ⟨L, hLfin, hL⟩
    -- Local instance justification (proof-local temporary data): use a basis for the finite intermediate field defining the Krull neighborhood.
    letI : FiniteDimensional F L := hLfin
    let b := Module.Basis.ofVectorSpace F L
    have hbasis : (⋂ i, {x : X | g x • (b i : E) = g x₀ • (b i : E)}) ∈ 𝓝 x₀ := by
      rw [iInter_mem]
      intro i
      let V : Set X := {x : X | g x • (b i : E) = g x₀ • (b i : E)}
      have hV : IsOpen V := by
        change IsOpen ((fun x : X ↦ g x • (b i : E)) ⁻¹' {g x₀ • (b i : E)})
        exact (isOpen_discrete _).preimage (hg_eval (b i : E))
      exact hV.mem_nhds rfl
    refine mem_of_superset hbasis ?_
    intro x hx
    apply hL
    change δ x ∈ L.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hfix : ∀ i, δ x (b i : E) = (b i : E) := by
      intro i
      have hi : g x • (b i : E) = g x₀ • (b i : E) := Set.mem_iInter.mp hx i
      calc
        δ x (b i : E) = (g x₀)⁻¹ • (g x • (b i : E)) := rfl
        _ = (g x₀)⁻¹ • (g x₀ • (b i : E)) := by rw [hi]
        _ = (b i : E) := by simp
    let incl : L →ₗ[F] E := (IsScalarTower.toAlgHom F L E).toLinearMap
    let φ : L →ₗ[F] E := (δ x).toLinearMap.comp incl
    have hlin : φ = incl := by
      apply b.ext
      intro i
      exact hfix i
    let yL : L := ⟨y, hy⟩
    have hy_fix : δ x y = y := by
      have h := congrArg (fun f : L →ₗ[F] E ↦ f yL) hlin
      simpa [φ, incl] using h
    exact hy_fix
  simpa [ContinuousAt, mul_assoc, δ] using hmul.const_mul (g x₀)

/-- Continuity of the action map
`(x, y) ↦ g x • y` on a discrete field implies continuity of `g` into its Krull-topological
Galois group. -/
theorem continuousOfContinuousGaloisAction
    (g : X → Gal(E/F))
    (hact : Continuous fun p : X × E ↦ g p.1 • p.2) :
    Continuous g := by
  exact continuousOfContinuousGaloisEval g <| continuous_prod_of_discrete_right.mp hact

end

end FieldExtension
