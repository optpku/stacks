/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Types.Stalks
public import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Data.Nat.Pairing

/-!
# Filter germs of function sheaves

This module relates stalks of sheaves of dependent functions to germs along an arbitrary filter.
The construction is expressed for a convergent map into a topological space and a map from its
fibres to a fixed target type. The constant-family specialization provides the usual map from a
function stalk to eventual values, while the filter-level infinitude result records the standard
tail quotient fact independently of any topological example.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Filter

noncomputable section

universe u v

namespace TopCat

namespace DependentFunctionStalk

variable {X : TopCat.{max u v}} {x : X}
variable {ι : Type v} {A : X → Type (max u v)} {B : Type (max u v)}

/-- Sends a dependent function on a neighborhood of `x` to its values along `f`, viewed as a
`Filter.Germ l B`; outside the neighborhood it uses the value at `x`. -/
def germLeg (toTarget : ∀ y : X, A y → B) (f : ι → X) (l : Filter ι)
    (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙ (X.sheafToTypes A).presheaf).obj U) ⟶ Filter.Germ l B :=
  ↾fun s ↦
    ((fun i ↦ @dite B (f i ∈ (unop U).1) (Classical.propDecidable _)
      (fun hi ↦ toTarget (f i) (s ⟨f i, hi⟩))
      (fun _ ↦ toTarget x (s ⟨x, (unop U).2⟩))) : Filter.Germ l B)

/-- The legs `germLeg` commute with restriction whenever `f` tends to `x` along `l`. -/
theorem germLeg_naturality (toTarget : ∀ y : X, A y → B) (f : ι → X) {l : Filter ι}
    (h_tendsto : Tendsto f l (nhds x)) {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙ (X.sheafToTypes A).presheaf).map i) ≫
        germLeg toTarget f l V =
      germLeg toTarget f l U := by
  ext s
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [h_tendsto.eventually ((unop V).1.isOpen.mem_nhds (unop V).2)] with j hj
  have hjV : f j ∈ (unop V).1 := hj
  have hjU : f j ∈ (unop U).1 := i.unop.le hj
  simp only [dif_pos hjV, dif_pos hjU]
  rfl

/-- The cocone presenting the germ of a dependent-function section along a convergent map. -/
def germCocone (toTarget : ∀ y : X, A y → B) (f : ι → X) {l : Filter ι}
    (h_tendsto : Tendsto f l (nhds x)) :
    Cocone ((OpenNhds.inclusion x).op ⋙ (X.sheafToTypes A).presheaf) where
  pt := Filter.Germ l B
  ι :=
    { app U := germLeg toTarget f l U
      naturality := fun _ _ i ↦ germLeg_naturality toTarget f h_tendsto i }

/-- The map from the stalk of a dependent-function sheaf at `x` to target-valued germs along a
map converging to `x`. -/
def toGerm (toTarget : ∀ y : X, A y → B) (f : ι → X) {l : Filter ι}
    (h_tendsto : Tendsto f l (nhds x)) :
    (X.sheafToTypes A).presheaf.stalk x ⟶ Filter.Germ l B :=
  colimit.desc _ (germCocone toTarget f h_tendsto)

/-- Computes `toGerm` on the germ of a section over an open neighborhood of `x`. -/
theorem toGerm_germ (toTarget : ∀ y : X, A y → B) (f : ι → X) {l : Filter ι}
    (h_tendsto : Tendsto f l (nhds x)) (U : Opens X) (hx : x ∈ U)
    (s : (X.sheafToTypes A).presheaf.obj (op U)) :
    toGerm toTarget f h_tendsto ((X.sheafToTypes A).presheaf.germ U x hx s) =
      ((fun i ↦ @dite B (f i ∈ U) (Classical.propDecidable _)
        (fun hi ↦ toTarget (f i) (s ⟨f i, hi⟩))
        (fun _ ↦ toTarget x (s ⟨x, hx⟩))) : Filter.Germ l B) := by
  change (colimit.desc _ (germCocone toTarget f h_tendsto))
    ((colimit.ι ((OpenNhds.inclusion x).op ⋙ (X.sheafToTypes A).presheaf)
      (op (⟨U, hx⟩ : OpenNhds x))) s) = _
  rw [← ConcreteCategory.comp_apply, colimit.ι_desc]
  rfl

/-- An extension operator realizing every target-valued function along `f` makes `toGerm`
surjective. -/
theorem toGerm_surjective_of_extension (toTarget : ∀ y : X, A y → B) (f : ι → X)
    {l : Filter ι} (h_tendsto : Tendsto f l (nhds x))
    (extend : (ι → B) → ∀ y : X, A y)
    (h_extend : ∀ (b : ι → B) (i : ι), toTarget (f i) (extend b (f i)) = b i) :
    Function.Surjective (toGerm toTarget f h_tendsto) := by
  intro g
  induction g using Filter.Germ.inductionOn with
  | h b =>
    refine ⟨(X.sheafToTypes A).presheaf.Γgerm x (fun y ↦ extend b y.1), ?_⟩
    rw [Presheaf.Γgerm, toGerm_germ]
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun i ↦ by simp [h_extend]

end DependentFunctionStalk

namespace FunctionStalk

variable {X : TopCat.{max u v}} {x : X} {ι : Type v}

/-- The stalk of the sheaf of `B`-valued functions maps to eventual `B`-valued functions along a
map converging to `x`. -/
def toGerm (B : Type (max u v)) (f : ι → X) {l : Filter ι}
    (h_tendsto : Tendsto f l (nhds x)) :
    (X.sheafToTypes fun _ : X ↦ B).presheaf.stalk x ⟶ Filter.Germ l B :=
  DependentFunctionStalk.toGerm (A := fun _ : X ↦ B) (fun _ ↦ id) f h_tendsto

/-- Computes the constant-family stalk-to-germ map on a global `B`-valued function. -/
theorem toGerm_Γgerm (B : Type (max u v)) (f : ι → X) {l : Filter ι}
    (h_tendsto : Tendsto f l (nhds x)) (s : X → B) :
    toGerm B f h_tendsto
        ((X.sheafToTypes fun _ : X ↦ B).presheaf.Γgerm x (fun y ↦ s y.1)) =
      (s ∘ f : Filter.Germ l B) := by
  unfold toGerm
  rw [Presheaf.Γgerm, DependentFunctionStalk.toGerm_germ]
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun i ↦ by simp

/-- A left inverse of a convergent map extends every `B`-valued function on its index type to a
global function, so the constant-family stalk-to-germ map is surjective. -/
theorem toGerm_surjective_of_leftInverse (B : Type (max u v)) (f : ι → X) {l : Filter ι}
    (h_tendsto : Tendsto f l (nhds x)) (retract : X → ι)
    (h_retract : Function.LeftInverse retract f) :
    Function.Surjective (toGerm B f h_tendsto) := by
  exact DependentFunctionStalk.toGerm_surjective_of_extension (fun _ ↦ id) f h_tendsto
    (fun b y ↦ b (retract y)) (fun b i ↦ congrArg b (h_retract i))

/-- If a convergent map from a nonempty index type is injective, every eventual `B`-valued
function is represented by a germ of a global `B`-valued function. -/
theorem toGerm_surjective_of_injective (B : Type (max u v)) [Nonempty ι] (f : ι → X)
    {l : Filter ι}
    (h_tendsto : Tendsto f l (nhds x)) (h_injective : Function.Injective f) :
    Function.Surjective (toGerm B f h_tendsto) := by
  obtain ⟨retract, h_retract⟩ := h_injective.hasLeftInverse
  exact toGerm_surjective_of_leftInverse B f h_tendsto retract h_retract

end FunctionStalk

namespace FunctionStalk

variable {X : TopCat.{u}} {x : X}

/-- A pairwise-distinct sequence converging to `x` prevents stalkwise evaluation of a
nontrivial constant function sheaf from being injective. -/
theorem toFiber_not_injective_of_tendsto_injective (B : Type u) [Nontrivial B] (f : ℕ → X)
    (h_tendsto : Tendsto f atTop (nhds x)) (h_injective : Function.Injective f) :
    ¬ Function.Injective (dependentFunctionStalkToFiber (fun _ : X ↦ B) x) := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne B
  intro h_eval
  have heval (s : X → B) :
      dependentFunctionStalkToFiber (fun _ : X ↦ B) x
          ((X.sheafToTypes fun _ : X ↦ B).presheaf.Γgerm x (fun y ↦ s y.1)) = s x := by
    change (colimit.desc _ (dependentFunctionStalkToFiberCocone (fun _ : X ↦ B) x))
      ((colimit.ι ((OpenNhds.inclusion x).op ⋙ (X.sheafToTypes fun _ : X ↦ B).presheaf)
        (op (⟨⊤, True.intro⟩ : OpenNhds x))) (fun y ↦ s y.1)) = s x
    rw [← ConcreteCategory.comp_apply, colimit.ι_desc]
    rfl
  have heq :
      (X.sheafToTypes fun _ : X ↦ B).presheaf.Γgerm x (fun _ ↦ a) =
        (X.sheafToTypes fun _ : X ↦ B).presheaf.Γgerm x
          (fun y ↦ if y.1 = x then a else b) := by
    apply h_eval
    exact (heval (fun _ ↦ a)).trans (by
      simpa using (heval (fun y ↦ if y = x then a else b)).symm)
  have htail := congrArg (toGerm B f h_tendsto) heq
  rw [toGerm_Γgerm B f h_tendsto (fun _ : X ↦ a),
    toGerm_Γgerm B f h_tendsto (fun y : X ↦ if y = x then a else b)] at htail
  have hevent := Filter.Germ.coe_eq.mp htail
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hx (n : ℕ) (hn : N ≤ n) : f n = x := by
    by_contra hnx
    exact hab (by simpa [Function.comp_apply, hnx] using hN n hn)
  have hindices : N = N + 1 := h_injective ((hx N le_rfl).trans (hx (N + 1) (Nat.le_succ N)).symm)
  exact (Nat.ne_of_lt (Nat.lt_succ_self N)) hindices

end FunctionStalk

end TopCat

namespace Filter.Germ

/-- A type with two distinct values has infinitely many distinct eventual tails along `atTop` on
`ℕ`. -/
theorem infinite_atTop_of_nontrivial (B : Type u) [Nontrivial B] :
    Infinite (Filter.Germ (Filter.atTop : Filter ℕ) B) := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne B
  -- The columns of a pairing function are disjoint infinite subsets of ℕ.
  let g : ℕ → Filter.Germ (Filter.atTop : Filter ℕ) B := fun n ↦
    ((fun k ↦ if (Nat.unpair k).1 = n then a else b) : Filter.Germ Filter.atTop B)
  apply Infinite.of_injective g
  intro m n h
  by_contra hmn
  have hevent := Filter.Germ.coe_eq.mp h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hvalues := hN (Nat.pair m N) (Nat.right_le_pair m N)
  exact hab (by simpa [Nat.unpair_pair, hmn] using hvalues)

end Filter.Germ
