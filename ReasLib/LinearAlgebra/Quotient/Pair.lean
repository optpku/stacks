module

public import ReasLib.LinearAlgebra.LinearMap.Pullback
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Tactic.Abel

/-!
# Paired submodule quotients

For submodules `S` and `T` of a module `M`, the canonical map
`M -> (M / S) x (M / T)` has kernel `S inf T`. Its range consists exactly of the pairs whose
images in `M / (S sup T)` agree. This is the module-theoretic fibre-product API behind quotient
patching arguments.

@stack 0H7M
-/

@[expose] public section

universe u v

namespace Submodule.Quotient

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The canonical map from a module to a pair of its submodule quotients. -/
@[stacks 0H7M "paired submodule quotient map"]
def pairMap (S T : Submodule R M) : M →ₗ[R] (M ⧸ S) × (M ⧸ T) :=
  S.mkQ.prod T.mkQ

/-- Pairs of quotient classes which have the same image modulo `S sup T`. -/
@[stacks 0H7M "compatible pairs of submodule quotients"]
def compatiblePairs (S T : Submodule R M) : Submodule R ((M ⧸ S) × (M ⧸ T)) :=
  LinearMap.pullback
    (Submodule.factor (le_sup_left : S ≤ S ⊔ T))
    (Submodule.factor (le_sup_right : T ≤ S ⊔ T))

@[simp]
theorem pairMap_apply (S T : Submodule R M) (x : M) :
    pairMap S T x = (S.mkQ x, T.mkQ x) :=
  rfl

@[simp]
theorem mem_compatiblePairs (S T : Submodule R M) (x : M ⧸ S) (y : M ⧸ T) :
    (x, y) ∈ compatiblePairs S T ↔
      Submodule.factor (le_sup_left : S ≤ S ⊔ T) x =
        Submodule.factor (le_sup_right : T ≤ S ⊔ T) y :=
  Iff.rfl

/-- The paired quotient map with codomain restricted to compatible pairs. -/
@[stacks 0H7M "paired quotient map into compatible pairs"]
def compatiblePairMap (S T : Submodule R M) :
    M →ₗ[R] compatiblePairs S T :=
  LinearMap.Pullback.lift
    (Submodule.factor (le_sup_left : S ≤ S ⊔ T))
    (Submodule.factor (le_sup_right : T ≤ S ⊔ T))
    S.mkQ T.mkQ (by ext x; rfl)

@[simp]
theorem compatiblePairMap_apply_val (S T : Submodule R M) (x : M) :
    ((compatiblePairMap S T x : compatiblePairs S T) : (M ⧸ S) × (M ⧸ T)) =
      (S.mkQ x, T.mkQ x) :=
  rfl

/-- The kernel of the paired quotient map is the intersection of the two submodules. -/
@[stacks 0H7M "kernel of the paired submodule quotient map"]
theorem ker_pairMap (S T : Submodule R M) :
    LinearMap.ker (pairMap S T) = S ⊓ T := by
  simp [pairMap, LinearMap.ker_prod]

/-- The paired quotient map is injective exactly when the two submodules have zero intersection. -/
@[stacks 0H7M "injectivity of the paired submodule quotient map"]
theorem pairMap_injective_iff (S T : Submodule R M) :
    Function.Injective (pairMap S T) ↔ S ⊓ T = ⊥ := by
  rw [← LinearMap.ker_eq_bot, ker_pairMap]

/-- The range of the paired quotient map is the submodule of compatible quotient pairs. -/
@[stacks 0H7M "range of the paired submodule quotient map"]
theorem range_pairMap (S T : Submodule R M) :
    LinearMap.range (pairMap S T) = compatiblePairs S T := by
  ext z
  rcases z with ⟨x, y⟩
  constructor
  · rintro ⟨m, hm⟩
    rw [← hm]
    simp
  · rw [mem_compatiblePairs]
    intro h
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective S x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective T y
    change (S ⊔ T).mkQ x = (S ⊔ T).mkQ y at h
    have hxy : x - y ∈ S ⊔ T := (Submodule.Quotient.eq (S ⊔ T)).mp h
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hxy
    refine ⟨x - s, ?_⟩
    rw [pairMap_apply]
    apply Prod.ext
    · change S.mkQ (x - s) = S.mkQ x
      apply (Submodule.Quotient.eq S).2
      have : (x - s) - x = -s := by abel
      rw [this]
      exact S.neg_mem hs
    · change T.mkQ (x - s) = T.mkQ y
      apply (Submodule.Quotient.eq T).2
      have : (x - s) - y = t := by
        calc
          (x - s) - y = (x - y) - s := by abel
          _ = (s + t) - s := by rw [hst]
          _ = t := by abel
      rw [this]
      exact ht

/-- Elementwise compatibility criterion for a pair of submodule quotient classes. -/
@[simp, stacks 0H7M "compatible pair criterion"]
theorem mem_range_pairMap_iff (S T : Submodule R M) (x : M ⧸ S) (y : M ⧸ T) :
    (x, y) ∈ LinearMap.range (pairMap S T) ↔
      Submodule.factor (le_sup_left : S ≤ S ⊔ T) x =
        Submodule.factor (le_sup_right : T ≤ S ⊔ T) y := by
  rw [range_pairMap, mem_compatiblePairs]

/-- Every compatible pair of quotient classes has a common representative. -/
@[stacks 0H7M "surjectivity onto compatible quotient pairs"]
theorem compatiblePairMap_surjective (S T : Submodule R M) :
    Function.Surjective (compatiblePairMap S T) := by
  intro z
  have hz : (z : (M ⧸ S) × (M ⧸ T)) ∈ LinearMap.range (pairMap S T) := by
    rw [range_pairMap]
    exact z.property
  rcases hz with ⟨x, hx⟩
  exact ⟨x, Subtype.ext hx⟩

/-- If `S inf T = 0`, the module is canonically equivalent to the compatible quotient pairs. -/
@[stacks 0H7M "module equivalence with compatible quotient pairs"]
noncomputable def compatiblePairsEquiv
    {S T : Submodule R M} (h : S ⊓ T = ⊥) :
    M ≃ₗ[R] compatiblePairs S T :=
  LinearEquiv.ofBijective (compatiblePairMap S T)
    ⟨by
      intro x y hxy
      apply ((pairMap_injective_iff S T).2 h)
      exact congrArg
        (fun z : compatiblePairs S T => (z : (M ⧸ S) × (M ⧸ T))) hxy,
    compatiblePairMap_surjective S T⟩

@[simp]
theorem compatiblePairsEquiv_apply
    {S T : Submodule R M} (h : S ⊓ T = ⊥) (x : M) :
    compatiblePairsEquiv h x = compatiblePairMap S T x :=
  rfl

/-- If `S inf T = 0`, the paired quotient map identifies `M` with its range. -/
@[stacks 0H7M "paired quotient range equivalence"]
theorem pairMap_rangeRestrict_bijective_of_inf_eq_bot
    {S T : Submodule R M} (h : S ⊓ T = ⊥) :
    Function.Bijective (pairMap S T).rangeRestrict := by
  exact ⟨(LinearMap.injective_rangeRestrict_iff (pairMap S T)).2
      ((pairMap_injective_iff S T).2 h),
    (pairMap S T).surjective_rangeRestrict⟩

end Submodule.Quotient
