/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Transition
public import ReasLib.CategoryTheory.InverseSystem.Sequential

@[expose] public section

/-!
# Lower-Truncation Resolution Towers

This leaf owns the algebraic data of a resolution tower over the canonical
lower truncations of a cochain complex.  The tower is represented as an object
of an under category, so its comparison map, cone, and map to its inverse
limit are available uniformly to every downstream construction.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty Opposite

noncomputable section

universe u v

namespace CochainComplex.LowerTruncation

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Stacks 070F: the truncation index of the `n`th lower-truncation stage. -/
@[stacks 070F]
abbrev index (n : ℕ) : ℤ := -((n + 1 : ℕ) : ℤ)

/-- Consecutive lower-truncation indices occur in the order required by the canonical
lower-truncation transition. -/
@[stacks 070F]
theorem index_succ_le (n : ℕ) : index (n + 1) ≤ index n := sorry

/-- Stacks 070F: the `n`th lower truncation of a cochain complex in the canonical sequential
tower. -/
@[stacks 070F]
abbrev stage (K : CochainComplex 𝒜 ℤ) (n : ℕ) : CochainComplex 𝒜 ℤ :=
  K.truncGE (index n)

/-- Stacks 070F: the successor transition in the canonical lower-truncation tower. -/
@[stacks 070F]
noncomputable def step (K : CochainComplex 𝒜 ℤ) (n : ℕ) :
    stage K (n + 1) ⟶ stage K n :=
  truncGEMapOfLE K (a := index (n + 1)) (b := index n)
    (neg_le_neg (Int.ofNat_le_ofNat_of_le (Nat.le_succ (n + 1))))

/-- The lower-truncation transition is compatible with the two canonical maps from the source
complex. -/
@[reassoc (attr := simp), stacks 070F]
theorem π_comp_step (K : CochainComplex 𝒜 ℤ) (n : ℕ) :
    K.πTruncGE (index (n + 1)) ≫ step K n = K.πTruncGE (index n) := sorry

/-- Stacks 070F: the sequential inverse system of canonical lower truncations of a cochain
complex. -/
@[stacks 070F]
noncomputable def diagram (K : CochainComplex 𝒜 ℤ) :
    SequentialInverseSystem (CochainComplex 𝒜 ℤ) :=
  Functor.ofOpSequence (step K)

/-- The successor map of the canonical lower-truncation diagram is its declared truncation
transition. -/
@[simp, stacks 070F]
theorem diagram_step (K : CochainComplex 𝒜 ℤ) (n : ℕ) :
    (diagram K).stepMap n = step K n := sorry

/-- Stacks 070F: a lower-truncation resolution tower of `K` with terms in `P`.

Each stage is a termwise-monomorphic, bounded-below, termwise-`P`
quasi-isomorphic model of the corresponding truncation.  Successor maps are
termwise split epimorphisms and have degreewise kernels in `P`. -/
@[stacks 070F]
structure Resolution (P : ObjectProperty 𝒜) (K : CochainComplex 𝒜 ℤ)
    extends Under (diagram K) where
  /-- The comparison at every stage is a bounded-below termwise-`P` quasi-isomorphic
  monomorphism. -/
  isResolutionStage (n : ℕ) :
    _root_.CochainComplex.Plus.TermsIn.Bounded.QuasiIso.Mono P (index n)
      (stage K n) (right.obj (op n)) (hom.app (op n))
  /-- Every successor map is split epic in every cochain degree. -/
  termwiseSplitEpi (n : ℕ) (i : ℤ) : IsSplitEpi ((right.stepMap n).f i)
  /-- The degreewise kernel of every successor map belongs to `P`. -/
  kernel_mem (n : ℕ) (i : ℤ) : P (kernel ((right.stepMap n).f i))

namespace Resolution

variable {P : ObjectProperty 𝒜} {K : CochainComplex 𝒜 ℤ}

/-- The inverse system of resolving complexes underlying a lower-truncation resolution. -/
abbrev tower (S : Resolution P K) :
    SequentialInverseSystem (CochainComplex 𝒜 ℤ) :=
  S.right

/-- The canonical natural transformation from the lower-truncation diagram to the resolving
tower. -/
abbrev comparison (S : Resolution P K) : diagram K ⟶ S.tower :=
  S.hom

/-- The `n`th resolving complex in a lower-truncation resolution. -/
abbrev stage (S : Resolution P K) (n : ℕ) : CochainComplex 𝒜 ℤ :=
  S.tower.obj (op n)

/-- The successor transition of a lower-truncation resolution. -/
abbrev step (S : Resolution P K) (n : ℕ) : S.stage (n + 1) ⟶ S.stage n :=
  S.tower.stepMap n

/-- The comparison map from the source complex to the `n`th resolving complex. -/
@[stacks 070F]
abbrev fromSource (S : Resolution P K) (n : ℕ) : K ⟶ S.stage n :=
  K.πTruncGE (index n) ≫ S.comparison.app (op n)

/-- The comparison at stage `n` is a quasi-isomorphism. -/
theorem comparison_quasiIso (S : Resolution P K) (n : ℕ) :
    QuasiIso (S.comparison.app (op n)) := sorry

/-- The resolving complex at stage `n` is zero strictly below its cutoff. -/
theorem stage_isStrictlyGE (S : Resolution P K) (n : ℕ) :
    (S.stage n).IsStrictlyGE (index n) := sorry

/-- Every term of every resolving stage belongs to `P`. -/
theorem stage_term_mem (S : Resolution P K) (n : ℕ) (i : ℤ) :
    P ((S.stage n).X i) := sorry

/-- The comparison at stage `n` is monomorphic. -/
theorem comparison_mono (S : Resolution P K) (n : ℕ) :
    Mono (S.comparison.app (op n)) := sorry

/-- Each successor map is split epimorphic in every degree. -/
theorem step_f_isSplitEpi (S : Resolution P K) (n : ℕ) (i : ℤ) :
    IsSplitEpi ((S.step n).f i) := sorry

attribute [instance] comparison_quasiIso stage_isStrictlyGE comparison_mono
  step_f_isSplitEpi

/-- Every component of a resolution-stage comparison is monomorphic. -/
instance comparison_f_mono (S : Resolution P K) (n : ℕ) (i : ℤ) :
    Mono ((S.comparison.app (op n)).f i) := sorry

/-- Every successor map in a resolving tower is epimorphic. -/
instance step_epi (S : Resolution P K) (n : ℕ) : Epi (S.step n) := sorry

/-- The degreewise kernel of a successor map belongs to `P`. -/
theorem step_kernel_mem (S : Resolution P K) (n : ℕ) (i : ℤ) :
    P (kernel ((S.step n).f i)) := sorry

/-- The comparison maps commute with the successor transitions of the two towers. -/
@[reassoc, stacks 070F]
theorem comparison_naturality (S : Resolution P K) (n : ℕ) :
    LowerTruncation.step K n ≫ S.comparison.app (op n) =
      S.comparison.app (op (n + 1)) ≫ S.step n := sorry

/-- The source-to-stage maps form a cone over the resolving tower. -/
@[reassoc, stacks 070F]
theorem fromSource_naturality (S : Resolution P K) (n : ℕ) :
    S.fromSource n = S.fromSource (n + 1) ≫ S.step n := sorry

/-- The cone-form naturality equation for source-to-stage maps, expressed in the form expected
by `NatTrans.ofOpSequence`. -/
@[stacks 070F]
theorem fromSource_naturality_ofOpSequence (S : Resolution P K) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj K).map (homOfLE (Nat.le_add_right n 1)).op ≫ S.fromSource n =
      S.fromSource (n + 1) ≫ S.tower.map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical cone from the source complex to the resolving tower. -/
@[stacks 070F]
noncomputable def cone (S : Resolution P K) : Cone S.tower where
  pt := K
  π := NatTrans.ofOpSequence (fun n ↦ S.fromSource n)
    (fun n ↦ S.fromSource_naturality_ofOpSequence n)

/-- The projection of the canonical resolution cone is the chosen
source-to-stage map. -/
@[simp, stacks 070F]
theorem cone_π_app (S : Resolution P K) (n : ℕ) :
    S.cone.π.app (op n) = S.fromSource n := sorry

/-- The canonical map from the source complex into the inverse limit of a lower-truncation
resolution.  This is also the map displayed in 21.24.0.1 (070P). -/
@[stacks 070F, stacks 070P "21.24.0.1: map into the candidate K-injective complex",
  stacks 071A "20.38.0.1: canonical map into a lower-truncation resolution limit"]
noncomputable abbrev intoLimit (S : Resolution P K) [HasLimit S.tower] :
    K ⟶ limit S.tower :=
  limit.lift S.tower S.cone

/-- The canonical map into the inverse limit has the expected projection to every resolving
stage. -/
@[reassoc (attr := simp), stacks 070F, stacks 071A
  "20.38.0.1: projection formula for the lower-truncation limit map"]
theorem intoLimit_comp_π (S : Resolution P K) [HasLimit S.tower] (n : ℕ) :
    S.intoLimit ≫ limit.π S.tower (op n) = S.fromSource n := sorry

/-- Maps into the limit of a lower-truncation resolution are equal when all their stage
projections are equal. -/
@[stacks 070F]
theorem hom_ext (S : Resolution P K) [HasLimit S.tower] {X : CochainComplex 𝒜 ℤ}
    {f g : X ⟶ limit S.tower}
    (h : ∀ n : ℕ, f ≫ limit.π S.tower (op n) = g ≫ limit.π S.tower (op n)) :
    f = g := sorry

/-- A map from the source complex to the inverse limit is the canonical map whenever all of its
stage projections are the canonical source-to-stage maps. -/
@[stacks 070F]
theorem eq_intoLimit_of_comp_π (S : Resolution P K) [HasLimit S.tower]
    {γ : K ⟶ limit S.tower}
    (hγ : ∀ n : ℕ, γ ≫ limit.π S.tower (op n) = S.fromSource n) :
    γ = S.intoLimit := sorry

/-- The projection characterization of the canonical map into the inverse limit. -/
@[stacks 070F]
theorem eq_intoLimit_iff (S : Resolution P K) [HasLimit S.tower]
    {γ : K ⟶ limit S.tower} :
    γ = S.intoLimit ↔
      ∀ n : ℕ, γ ≫ limit.π S.tower (op n) = S.fromSource n := sorry

end Resolution

/-- Stacks 070F: every cochain complex has a lower-truncation resolution tower when `P`
contains zero, is closed under finite products, and admits monomorphic embeddings. -/
@[stacks 070F]
theorem exists_resolution (P : ObjectProperty 𝒜) [P.ContainsZero]
    [P.IsClosedUnderFiniteProducts] [P.HasMonoEmbedding] (K : CochainComplex 𝒜 ℤ) :
    Nonempty (Resolution P K) := sorry

end CochainComplex.LowerTruncation
