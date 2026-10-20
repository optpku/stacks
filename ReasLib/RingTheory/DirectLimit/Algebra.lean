module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Compatible direct systems of commutative algebras

This leaf supplies the small algebra-facing layer over mathlib's raw
`Ring.DirectLimit` construction.  In particular, a compatible family of ring
maps between two systems induces an explicit algebra structure on their direct
limits.  It deliberately does not register that structure as a global
instance: its coherence proof is genuine input data and cannot be recovered
from the two direct-limit rings alone.
-/

@[expose] public section

universe u v w

noncomputable section

namespace Ring.DirectLimit

namespace Algebra

variable {I : Type u} [Preorder I]
variable {R : I → Type v} {S : I → Type w}
variable [∀ i, CommRing (R i)] [∀ i, CommRing (S i)]
variable {ρ : ∀ i j, i ≤ j → R i →+* R j}
variable {σ : ∀ i j, i ≤ j → S i →+* S j}

/-- The canonical map from a stage of a commutative-ring direct system to its
direct limit induces an algebra structure on the direct limit over that stage.
The stage is explicit because the target alone does not select one stage;
registering every such action globally would create competing algebra instances. -/
@[reducible, stacks 05LI "direct-limit stage algebra"]
noncomputable def stageAlgebra
    {A : I → Type v} [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j) (i : I) :
    Algebra (A i) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
  (Ring.DirectLimit.of A (fun i j h ↦ f i j h) i).toAlgebra

/-- The algebra map of the stage-indexed direct-limit algebra is the canonical
map from that stage. -/
@[stacks 05LI "direct-limit stage algebra"]
theorem stageAlgebra_algebraMap
    {A : I → Type v} [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j) (i : I) :
    -- Local instance justification (noncanonical choice): `f` and stage `i` select the action; the direct-limit carrier does not determine it.
    letI : Algebra (A i) (Ring.DirectLimit A (fun i j h ↦ f i j h)) := stageAlgebra f i
    algebraMap (A i) (Ring.DirectLimit A (fun i j h ↦ f i j h)) =
      Ring.DirectLimit.of A (fun i j h ↦ f i j h) i := sorry

/-- The algebra structures induced by two comparable stages form the expected
scalar tower over the direct limit. -/
@[stacks 05LI "direct-limit stage algebra"]
theorem stageAlgebra_isScalarTower
    {A : I → Type v} [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j) {i j : I} (hij : i ≤ j) :
    -- Local instance justification (noncanonical choice): `f` and source stage `i` select the action; the direct-limit carrier does not determine it.
    letI : Algebra (A i) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
      stageAlgebra f i
    -- Local instance justification (noncanonical choice): transition `f i j hij` selects the action; the stage carriers do not determine it.
    letI : Algebra (A i) (A j) := (f i j hij).toAlgebra
    -- Local instance justification (noncanonical choice): `f` and target stage `j` select the action; the direct-limit carrier does not determine it.
    letI : Algebra (A j) (Ring.DirectLimit A (fun i j h ↦ f i j h)) :=
      stageAlgebra f j
    IsScalarTower (A i) (A j) (Ring.DirectLimit A (fun i j h ↦ f i j h)) := sorry

/-- The canonical stage maps into a ring direct limit respect a transition. -/
@[stacks 07BQ "direct-limit stage map"]
theorem of_comp {A : I → Type v} [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j) {i j : I} (h : i ≤ j) :
    (Ring.DirectLimit.of A (fun i j h ↦ f i j h) j).comp (f i j h) =
      Ring.DirectLimit.of A (fun i j h ↦ f i j h) i := sorry

/-- Canonical stage maps commute pointwise with a transition map. -/
@[simp, stacks 07BQ "direct-limit stage map"]
theorem of_transition {A : I → Type v} [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j) {i j : I} (h : i ≤ j) (x : A i) :
    Ring.DirectLimit.of A (fun i j h ↦ f i j h) j (f i j h x) =
      Ring.DirectLimit.of A (fun i j h ↦ f i j h) i x := sorry

/-- A compatible family of maps between ring systems commutes with the maps
from every source stage into the two direct limits. -/
@[stacks 07BQ "direct-limit map"]
theorem map_comp_of
    (g : ∀ i, R i →+* S i)
    (hcomm : ∀ ⦃i j : I⦄ (h : i ≤ j), (g j).comp (ρ i j h) = (σ i j h).comp (g i))
    (i : I) :
    (Ring.DirectLimit.map g (fun _ _ h ↦ hcomm h)).comp
        (Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i) =
      (Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i).comp (g i) := sorry

/-- A compatible direct-limit map evaluates on a stage generator by the
corresponding stage map. -/
@[simp, stacks 07BQ "direct-limit map"]
theorem map_of
    (g : ∀ i, R i →+* S i)
    (hcomm : ∀ ⦃i j : I⦄ (h : i ≤ j), (g j).comp (ρ i j h) = (σ i j h).comp (g i))
    (i : I) (x : R i) :
    Ring.DirectLimit.map g (fun _ _ h ↦ hcomm h)
        (Ring.DirectLimit.of R (fun i j h ↦ ρ i j h) i x) =
      Ring.DirectLimit.of S (fun i j h ↦ σ i j h) i (g i x) := sorry

/-- A compatible family of maps between commutative-ring systems equips the
target direct limit with an explicit algebra structure over the source direct
limit.  The coherence proof remains an explicit parameter, so this is a
constructor rather than a global instance. -/
@[stacks 07BQ "direct-limit algebra structure", reducible]
noncomputable def mapAlgebra
    (g : ∀ i, R i →+* S i)
    (hcomm : ∀ ⦃i j : I⦄ (h : i ≤ j), (g j).comp (ρ i j h) = (σ i j h).comp (g i)) :
    Algebra (Ring.DirectLimit R (fun i j h ↦ ρ i j h))
      (Ring.DirectLimit S (fun i j h ↦ σ i j h)) :=
  (Ring.DirectLimit.map g fun _ _ h ↦ hcomm h).toAlgebra

/-- The algebra map of a compatible map between direct-limit systems is the
induced map of their direct limits. -/
@[stacks 07BQ "direct-limit algebra structure"]
theorem mapAlgebra_algebraMap
    (g : ∀ i, R i →+* S i)
    (hcomm : ∀ ⦃i j : I⦄ (h : i ≤ j), (g j).comp (ρ i j h) = (σ i j h).comp (g i)) :
    -- Local instance justification (noncanonical choice): compatible maps `g` and `hcomm` select the action; the direct-limit carriers do not determine it.
    letI : Algebra (Ring.DirectLimit R (fun i j h ↦ ρ i j h))
      (Ring.DirectLimit S (fun i j h ↦ σ i j h)) := mapAlgebra g hcomm
    algebraMap (Ring.DirectLimit R (fun i j h ↦ ρ i j h))
        (Ring.DirectLimit S (fun i j h ↦ σ i j h)) =
      Ring.DirectLimit.map g (fun _ _ h ↦ hcomm h) := sorry

end Algebra

end Ring.DirectLimit
