/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Sequential Diagrams in Preadditive Categories

This leaf owns the algebraic telescope map of a sequential diagram and the
finite-prefix systems used to analyse it.  It is independent of
pretriangulated and derived categories: only preadditive structure, finite
biproducts, and the colimits explicitly requested by each construction are
used here.

The `FinitePrefix` namespace contains one fixed, recursively bracketed model
of the finite partial sums.  Its maps are useful when a downstream argument
needs concrete finite-stage calculations; `telescopeMap_shortExact` is the
high-level consequence for abelian categories with exact sequential colimits.
-/

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

universe v u

noncomputable section

namespace CategoryTheory.Limits.Sequential

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The algebraic telescope endomorphism `1 - f` of the coproduct of a sequential diagram. -/
@[stacks 093W]
def telescopeMap (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    ∐ K.obj ⟶ ∐ K.obj :=
  𝟙 _ - Sigma.map' Nat.succ (fun n ↦ K.map (homOfLE (Nat.le_succ n)))

/-- The `n`th summand of `telescopeMap K` is the difference of the identity and the successor
transition. -/
@[reassoc]
theorem ι_comp_telescopeMap (K : ℕ ⥤ C) [HasCoproduct K.obj] (n : ℕ) :
    Sigma.ι K.obj n ≫ telescopeMap K =
      Sigma.ι K.obj n - K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := sorry

attribute [simp] ι_comp_telescopeMap_assoc

/-- The telescope endomorphism is natural in a morphism of sequential diagrams. -/
@[reassoc]
theorem telescopeMap_naturality {K L : ℕ ⥤ C}
    [HasCoproduct K.obj] [HasCoproduct L.obj] (φ : K ⟶ L) :
    telescopeMap K ≫ Sigma.map φ.app = Sigma.map φ.app ≫ telescopeMap L := sorry

/-- The telescope map vanishes after a coproduct descent whose legs form a cocone over the
sequential diagram. -/
@[reassoc]
theorem telescopeMap_comp_sigmaDesc (K : ℕ ⥤ C) [HasCoproduct K.obj] {X : C}
    (ι : ∀ n, K.obj n ⟶ X)
    (hι : ∀ n, K.map (homOfLE (Nat.le_succ n)) ≫ ι (n + 1) = ι n) :
    telescopeMap K ≫ Sigma.desc ι = 0 := sorry

/-- The telescope map vanishes after the coproduct descent of any cocone over the sequential
diagram. -/
@[reassoc]
theorem telescopeMap_comp_sigmaDesc_of_cocone (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (c : Cocone K) :
    telescopeMap K ≫ Sigma.desc (fun n ↦ c.ι.app n) = 0 := sorry

/-- The canonical short complex whose first map is the telescope endomorphism and whose
second map is the coproduct descent to the sequential colimit. -/
@[stacks 093W]
noncomputable def telescopeShortComplex (K : ℕ ⥤ C) [HasCoproduct K.obj] [HasColimit K] :
    ShortComplex C :=
  ShortComplex.mk (telescopeMap K)
    (Sigma.desc (colimit.ι K))
    (telescopeMap_comp_sigmaDesc K (colimit.ι K)
      (fun n ↦ colimit.w K (homOfLE (Nat.le_succ n))))

/-- The projection from the coproduct of a sequential diagram to its `k`th object, retaining
summands indexed by `i ≤ k` through their transition maps and killing later summands. -/
noncomputable def prefixProjection (K : ℕ ⥤ C) [HasCoproduct K.obj] (k : ℕ) :
    ∐ K.obj ⟶ K.obj k :=
  Sigma.desc fun i ↦ if h : i ≤ k then K.map (homOfLE h) else 0

/-- A retained summand maps through `prefixProjection` by its sequential transition map. -/
@[reassoc]
theorem sigma_ι_comp_prefixProjection_of_le (K : ℕ ⥤ C) [HasCoproduct K.obj]
    {i k : ℕ} (h : i ≤ k) :
    Sigma.ι K.obj i ≫ prefixProjection K k = K.map (homOfLE h) := sorry

/-- A summand after the selected prefix is killed by `prefixProjection`. -/
@[reassoc]
theorem sigma_ι_comp_prefixProjection_of_not_le (K : ℕ ⥤ C) [HasCoproduct K.obj]
    {i k : ℕ} (h : ¬ i ≤ k) :
    Sigma.ι K.obj i ≫ prefixProjection K k = 0 := sorry

/-- The `k`th summand is sent identically to the `k`th object by `prefixProjection`. -/
@[reassoc]
theorem sigma_ι_comp_prefixProjection_self (K : ℕ ⥤ C) [HasCoproduct K.obj] (k : ℕ) :
    Sigma.ι K.obj k ≫ prefixProjection K k = 𝟙 (K.obj k) := sorry

end

namespace FinitePrefix

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

/-- A recursively bracketed finite partial sum of a sequential diagram.  `obj K n` contains the
terms with indices strictly smaller than `n`. -/
def obj (K : ℕ ⥤ C) : ℕ → C
  | 0 => 0
  | n + 1 => obj K n ⊞ K.obj n

/-- The canonical inclusion of a finite prefix into the prefix with one additional summand. -/
def inclusion (K : ℕ ⥤ C) (n : ℕ) :
    obj K n ⟶ obj K (n + 1) :=
  biprod.inl

/-- The inclusion of the newest summand into a nonempty finite prefix. -/
def lastι (K : ℕ ⥤ C) (n : ℕ) :
    K.obj n ⟶ obj K (n + 1) :=
  biprod.inr

/-- The recursive projection from a nonempty finite prefix to its newest quotient summand. -/
def stageProjection (K : ℕ ⥤ C) :
    (n : ℕ) → obj K (n + 1) ⟶ K.obj n
  | 0 => biprod.snd
  | n + 1 =>
      biprod.desc
        (stageProjection K n ≫ K.map (homOfLE (Nat.le_succ n)))
        (𝟙 _)

/-- The finite-stage telescope map from one partial sum to the next. -/
def stageMap (K : ℕ ⥤ C) :
    (n : ℕ) → obj K n ⟶ obj K (n + 1)
  | 0 => inclusion K 0
  | n + 1 =>
      biprod.desc
        (stageMap K n ≫ inclusion K (n + 1))
        (lastι K n ≫ inclusion K (n + 1) -
          K.map (homOfLE (Nat.le_succ n)) ≫ lastι K (n + 1))

/-- A recursive retraction of the finite-stage telescope map. -/
def stageRetraction (K : ℕ ⥤ C) :
    (n : ℕ) → obj K (n + 1) ⟶ obj K n
  | 0 => biprod.fst
  | n + 1 =>
      biprod.desc
        (biprod.lift (stageRetraction K n) (stageProjection K n))
        0

/-- The newest summand maps isomorphically to its stage quotient. -/
theorem lastι_comp_stageProjection (K : ℕ ⥤ C) (n : ℕ) :
    lastι K n ≫ stageProjection K n = 𝟙 _ := sorry

/-- The recursive stage retraction annihilates the newest summand. -/
theorem lastι_comp_stageRetraction (K : ℕ ⥤ C) (n : ℕ) :
    lastι K n ≫ stageRetraction K n = 0 := sorry

/-- The old-prefix inclusion followed by the next stage projection is the previous projection
followed by the sequential transition. -/
theorem inclusion_comp_stageProjection (K : ℕ ⥤ C) (n : ℕ) :
    inclusion K (n + 1) ≫ stageProjection K (n + 1) =
      stageProjection K n ≫ K.map (homOfLE (Nat.le_succ n)) := sorry

/-- The correction branch of a finite-stage telescope map vanishes after the next stage
projection. -/
theorem correction_comp_stageProjection (K : ℕ ⥤ C) (n : ℕ) :
    ((lastι K n ≫ inclusion K (n + 1)) -
        (K.map (homOfLE (Nat.le_succ n)) ≫ lastι K (n + 1))) ≫
      stageProjection K (n + 1) = 0 := sorry

/-- Every finite-stage telescope map is annihilated by its stage projection. -/
theorem stageMap_comp_stageProjection (K : ℕ ⥤ C) (n : ℕ) :
    stageMap K n ≫ stageProjection K n = 0 := sorry

/-- Every finite-stage telescope map is split mono. -/
theorem stageSplitMono (K : ℕ ⥤ C) (n : ℕ) :
    IsSplitMono (stageMap K n) := sorry

/-- Every finite-stage telescope map is mono. -/
theorem stageMono (K : ℕ ⥤ C) (n : ℕ) :
    Mono (stageMap K n) := sorry

/-- The chosen finite prefixes form a sequential diagram. -/
def source (K : ℕ ⥤ C) : ℕ ⥤ C :=
  Functor.ofSequence (fun n ↦ inclusion K n)

/-- The shifted finite prefixes form a second sequential diagram. -/
def target (K : ℕ ⥤ C) : ℕ ⥤ C :=
  Functor.ofSequence (X := fun n ↦ obj K (n + 1))
    (fun n ↦ inclusion K (n + 1))

/-- The finite-stage telescope maps obey the successor naturality relation. -/
theorem stageNaturality (K : ℕ ⥤ C) (n : ℕ) :
    inclusion K n ≫ stageMap K (n + 1) =
      stageMap K n ≫ inclusion K (n + 1) := sorry

/-- The same relation, expressed using the source and target sequence functors. -/
theorem stageNatTrans_naturality (K : ℕ ⥤ C) (n : ℕ) :
    (source K).map (homOfLE (Nat.le_succ n)) ≫ stageMap K (n + 1) =
      stageMap K n ≫ (target K).map (homOfLE (Nat.le_succ n)) := sorry

/-- The finite-stage telescope maps assemble into a natural transformation of sequential
diagrams. -/
def stageNatTrans (K : ℕ ⥤ C) : source K ⟶ target K :=
  NatTrans.ofSequence (fun n ↦ stageMap K n) (stageNatTrans_naturality K)

/-- The canonical map from a finite prefix into the coproduct of the whole sequence. -/
def toCoproduct (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    (n : ℕ) → obj K n ⟶ ∐ K.obj
  | 0 => 0
  | n + 1 => biprod.desc (toCoproduct K n) (Sigma.ι K.obj n)

/-- A prefix inclusion is compatible with the maps into the coproduct. -/
theorem inclusion_comp_toCoproduct (K : ℕ ⥤ C)
    [HasCoproduct K.obj] (n : ℕ) :
    inclusion K n ≫ toCoproduct K (n + 1) = toCoproduct K n := sorry

/-- The newest summand of a prefix maps to the corresponding coproduct inclusion. -/
theorem lastι_comp_toCoproduct (K : ℕ ⥤ C)
    [HasCoproduct K.obj] (n : ℕ) :
    lastι K n ≫ toCoproduct K (n + 1) = Sigma.ι K.obj n := sorry

/-- The correction branch maps to the difference of the two adjacent coproduct summands. -/
theorem correction_comp_toCoproduct (K : ℕ ⥤ C)
    [HasCoproduct K.obj] (n : ℕ) :
    ((lastι K n ≫ inclusion K (n + 1)) -
        (K.map (homOfLE (Nat.le_succ n)) ≫ lastι K (n + 1))) ≫
      toCoproduct K (n + 2) =
        Sigma.ι K.obj n - K.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι K.obj (n + 1) := sorry

/-- The maps from finite prefixes to the coproduct intertwine the finite-stage and global
telescope maps. -/
theorem toCoproduct_comp_telescopeMap (K : ℕ ⥤ C)
    [HasCoproduct K.obj] (n : ℕ) :
    toCoproduct K n ≫ telescopeMap K = stageMap K n ≫ toCoproduct K (n + 1) := sorry

/-- The source-prefix cocone legs satisfy their successor compatibility relation. -/
theorem sourceCocone_naturality (K : ℕ ⥤ C)
    [HasCoproduct K.obj] (n : ℕ) :
    (source K).map (homOfLE (Nat.le_succ n)) ≫ toCoproduct K (n + 1) =
      toCoproduct K n ≫ ((Functor.const ℕ).obj (∐ K.obj)).map
        (homOfLE (Nat.le_succ n)) := sorry

/-- The target-prefix cocone legs satisfy their successor compatibility relation. -/
theorem targetCocone_naturality (K : ℕ ⥤ C)
    [HasCoproduct K.obj] (n : ℕ) :
    (target K).map (homOfLE (Nat.le_succ n)) ≫ toCoproduct K (n + 2) =
      toCoproduct K (n + 1) ≫ ((Functor.const ℕ).obj (∐ K.obj)).map
        (homOfLE (Nat.le_succ n)) := sorry

/-- The cocone from the source-prefix sequence to the coproduct. -/
def sourceCocone (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    Cocone (source K) :=
  Cocone.mk (∐ K.obj) <|
    NatTrans.ofSequence (fun n ↦ toCoproduct K n) (sourceCocone_naturality K)

/-- The cocone from the target-prefix sequence to the coproduct. -/
def targetCocone (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    Cocone (target K) :=
  Cocone.mk (∐ K.obj) <|
    NatTrans.ofSequence (fun n ↦ toCoproduct K (n + 1)) (targetCocone_naturality K)

/-- The explicit descendant from the coproduct for a cocone on the source-prefix sequence. -/
def sourceDesc (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (s : Cocone (source K)) :
    (∐ K.obj) ⟶ s.pt :=
  Sigma.desc (fun i ↦ lastι K i ≫ s.ι.app (i + 1))

/-- The source-prefix descendant has the required components. -/
@[simp, reassoc]
theorem sourceDesc_fac (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (s : Cocone (source K)) (n : ℕ) :
    toCoproduct K n ≫ sourceDesc K s = s.ι.app n := sorry

/-- The source-prefix descendant is the unique map satisfying the cocone equations. -/
theorem sourceDesc_uniq (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (s : Cocone (source K)) (m : (sourceCocone K).pt ⟶ s.pt)
    (hm : ∀ n, (sourceCocone K).ι.app n ≫ m = s.ι.app n) :
    m = sourceDesc K s := sorry

/-- The coproduct is a colimit of the source-prefix sequential diagram. -/
noncomputable def sourceIsColimit (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    IsColimit (sourceCocone K) :=
  IsColimit.mk
    (fun s ↦ sourceDesc K s)
    (fun s n ↦ sourceDesc_fac K s n)
    (fun s m hm ↦ sourceDesc_uniq K s m hm)

/-- The explicit descendant from the coproduct for a cocone on the target-prefix sequence. -/
def targetDesc (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (s : Cocone (target K)) :
    (∐ K.obj) ⟶ s.pt :=
  Sigma.desc (fun i ↦ lastι K i ≫ s.ι.app i)

/-- The target-prefix descendant has the required components. -/
@[simp, reassoc]
theorem targetDesc_fac (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (s : Cocone (target K)) (n : ℕ) :
    toCoproduct K (n + 1) ≫ targetDesc K s = s.ι.app n := sorry

/-- The target-prefix descendant is the unique map satisfying the cocone equations. -/
theorem targetDesc_uniq (K : ℕ ⥤ C) [HasCoproduct K.obj]
    (s : Cocone (target K)) (m : (targetCocone K).pt ⟶ s.pt)
    (hm : ∀ n, (targetCocone K).ι.app n ≫ m = s.ι.app n) :
    m = targetDesc K s := sorry

/-- The coproduct is a colimit of the target-prefix sequential diagram. -/
noncomputable def targetIsColimit (K : ℕ ⥤ C) [HasCoproduct K.obj] :
    IsColimit (targetCocone K) :=
  IsColimit.mk
    (fun s ↦ targetDesc K s)
    (fun s n ↦ targetDesc_fac K s n)
    (fun s m hm ↦ targetDesc_uniq K s m hm)

/-- The source and target finite-prefix cocones intertwine the finite-stage and global telescope
maps. -/
theorem coconeCompat (K : ℕ ⥤ C) [HasCoproduct K.obj] (n : ℕ) :
    (sourceCocone K).ι.app n ≫ telescopeMap K =
      (stageNatTrans K).app n ≫ (targetCocone K).ι.app n := sorry

end

end FinitePrefix

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasColimitsOfShape ℕ C]

/-- The telescope short complex of a sequential diagram is short exact when sequential colimits
are exact.  This is the high-level API; `FinitePrefix` exposes the concrete finite-stage model
used to establish its monomorphism assertion. -/
@[stacks 093W]
theorem telescopeMap_shortExact [HasExactColimitsOfShape ℕ C] (K : ℕ ⥤ C)
    [HasCoproduct K.obj] :
    (telescopeShortComplex K).ShortExact := sorry

end

end CategoryTheory.Limits.Sequential
