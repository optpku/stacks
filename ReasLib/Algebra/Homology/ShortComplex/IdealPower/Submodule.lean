module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.Algebra.Homology.ShortComplex.Noetherian
public import ReasLib.Algebra.Module.IdealPower.Submodule
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of adic submodule stages

This file owns the filtered-homology systems attached to a short complex of modules.  The
quotient-stage systems from `...ShortComplex.IdealPower` are a different construction and are
kept separate.  In particular, the stage at `n` here is the short complex obtained by taking
`I ^ n • ⊤` in each term.

@stack 0G3K
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.ShortComplex.IdealPower.Submodule

variable {A : Type u} [CommRing A]

/-- The short complex obtained by taking the `n`th adic stage termwise. -/
@[stacks 0G3K "adic stage of a short complex"]
abbrev stage (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    ShortComplex (ModuleCat.{v} A) :=
  S.map (Ideal.PowerSubmodule.functor I n)

/-- The homology module of the `n`th adic stage complex. -/
@[stacks 0G3K "adic stage homology"]
abbrev homologyStage (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    ModuleCat.{v} A :=
  (stage S I n).moduleCatLeftHomologyData.H

/-- The explicit stage-to-ambient morphism of short complexes. -/
@[stacks 0G3K "adic stage short-complex inclusion"]
noncomputable def subtypeMap
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    stage S I n ⟶ S where
  τ₁ := ModuleCat.ofHom (Ideal.PowerSubmodule.subtype I S.X₁ n)
  τ₂ := ModuleCat.ofHom (Ideal.PowerSubmodule.subtype I S.X₂ n)
  τ₃ := ModuleCat.ofHom (Ideal.PowerSubmodule.subtype I S.X₃ n)
  comm₁₂ := sorry
  comm₂₃ := sorry

/-- The explicit transition morphism between two adic stage complexes. -/
@[stacks 0G3K "adic stage short-complex transition"]
noncomputable def inclusionMap
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    stage S I n ⟶ stage S I m where
  τ₁ := Ideal.PowerSubmodule.inclusion I S.X₁ h
  τ₂ := Ideal.PowerSubmodule.inclusion I S.X₂ h
  τ₃ := Ideal.PowerSubmodule.inclusion I S.X₃ h
  comm₁₂ := sorry
  comm₂₃ := sorry

/-- Passing through a shallower stage and then to the ambient complex is the direct inclusion. -/
@[stacks 0G3K "adic stage short-complex inclusions compose"]
theorem inclusionMap_comp_subtypeMap
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    inclusionMap S I h ≫ subtypeMap S I m = subtypeMap S I n := sorry

/-- The canonical map from stage homology to ambient homology. -/
@[stacks 0G3K "adic stage homology to ambient homology"]
noncomputable abbrev toAmbient (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    homologyStage S I n ⟶ S.moduleCatLeftHomologyData.H :=
  leftHomologyMap' (subtypeMap S I n) (stage S I n).moduleCatLeftHomologyData
    S.moduleCatLeftHomologyData

/-- The transition map on the homology modules of adic stage complexes. -/
@[stacks 0G3K "adic stage homology transition"]
noncomputable abbrev homologyTransition
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    homologyStage S I n ⟶ homologyStage S I m :=
  leftHomologyMap' (inclusionMap S I h) (stage S I n).moduleCatLeftHomologyData
    (stage S I m).moduleCatLeftHomologyData

/-- The successor map on the adic-stage homology tower. -/
@[stacks 0G3K "adic stage homology successor"]
noncomputable abbrev homologyStep
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    homologyStage S I (n + 1) ⟶ homologyStage S I n :=
  homologyTransition S I (Nat.le_succ n)

/-- The inverse system of homology modules of the adic stage complexes. -/
@[stacks 0G3K "adic stage homology tower"]
noncomputable def tower (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) :
    SequentialInverseSystem (ModuleCat.{v} A) :=
  Functor.ofOpSequence (fun n ↦ homologyStep S I n)

/-- The `n`th stage in the adic filtration of the ambient homology. -/
@[stacks 0G3K "ambient adic homology stage"]
abbrev ambientStage (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    ModuleCat.{v} A :=
  Ideal.PowerSubmodule.stageObj I S.moduleCatLeftHomologyData.H n

/-- The transition map on the adic stages of ambient homology. -/
@[stacks 0G3K "ambient adic homology transition"]
abbrev ambientTransition (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A)
    {m n : ℕ} (h : m ≤ n) : ambientStage S I n ⟶ ambientStage S I m :=
  Ideal.PowerSubmodule.inclusion I S.moduleCatLeftHomologyData.H h

/-- The inverse system of adic stages of ambient homology. -/
@[stacks 0G3K "ambient adic homology tower"]
noncomputable def ambientTower (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) :
    SequentialInverseSystem (ModuleCat.{v} A) :=
  Functor.ofOpSequence (fun n ↦ ambientTransition S I (Nat.le_succ n))

/-- The object formula for the filtered-homology tower. -/
@[stacks 0G3K "adic homology tower object formula"]
theorem tower_obj (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    (tower S I).obj (Opposite.op n) = homologyStage S I n := sorry

/-- The object formula for the ambient adic homology tower. -/
@[stacks 0G3K "ambient adic tower object formula"]
theorem ambientTower_obj (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    (ambientTower S I).obj (Opposite.op n) = ambientStage S I n := sorry

/-- The successor map of the filtered-homology tower is its declared homology transition. -/
@[simp, stacks 0G3K "adic homology tower successor formula"]
theorem tower_stepMap (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    (tower S I).stepMap n = homologyStep S I n := sorry

/-- Every map in the filtered-homology tower is the canonical endpoint transition. -/
@[stacks 0G3K "adic homology tower transition formula"]
theorem tower_transitionMap
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    (tower S I).transitionMap h = homologyTransition S I h := sorry

/-- The successor map of the ambient adic tower is its declared stage inclusion. -/
@[simp, stacks 0G3K "ambient adic tower successor formula"]
theorem ambientTower_stepMap
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    (ambientTower S I).stepMap n = ambientTransition S I (Nat.le_succ n) := sorry

/-- Every map in the ambient adic tower is the canonical endpoint inclusion. -/
@[stacks 0G3K "ambient adic tower transition formula"]
theorem ambientTower_transitionMap
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    (ambientTower S I).transitionMap h = ambientTransition S I h := sorry

/-- A homology transition followed by the ambient map is the direct ambient map. -/
@[stacks 0G3K "adic homology transition to ambient"]
theorem homologyTransition_comp_toAmbient
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    homologyTransition S I h ≫ toAmbient S I m = toAmbient S I n := sorry

/-- The `n`th adic stage of the ambient cycle module. -/
@[stacks 0G3K "adic stage of ambient cycles"]
abbrev cyclesStage (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    ModuleCat.{v} A :=
  Ideal.PowerSubmodule.stageObj I S.moduleCatLeftHomologyData.K n

/-- The adic stage of cycles maps onto the corresponding stage of ambient homology. -/
@[stacks 0G3K "adic cycles to ambient homology stage"]
noncomputable abbrev cyclesStageToAmbient
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    cyclesStage S I n ⟶ ambientStage S I n :=
  Ideal.PowerSubmodule.mapObj I S.moduleCatLeftHomologyData.π n

/-- An adic-stage ambient cycle viewed in the middle term of the original short complex. -/
@[stacks 0G3K "adic ambient cycle representative"]
abbrev cyclesStageToMiddle
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (n : ℕ) :
    cyclesStage S I n ⟶ S.X₂ :=
  ModuleCat.ofHom (Ideal.PowerSubmodule.subtype I S.moduleCatLeftHomologyData.K n) ≫
    S.moduleCatLeftHomologyData.i

/-- A cycle of an adic-stage complex viewed in the middle term of the original complex. -/
@[stacks 0G3K "adic stage cycle representative"]
noncomputable abbrev stageCyclesToMiddle
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (m : ℕ) :
    (stage S I m).moduleCatLeftHomologyData.K ⟶ S.X₂ :=
  (stage S I m).moduleCatLeftHomologyData.i ≫ (subtypeMap S I m).τ₂

/-- The canonical middle-term map from a deep ambient-cycle stage to a shallower complex stage. -/
@[stacks 0G3K "canonical adic cycle map to a shallower middle stage"]
noncomputable abbrev cyclesStageToStageMiddle
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    cyclesStage S I n ⟶ (stage S I m).X₂ :=
  Ideal.PowerSubmodule.mapObj I S.moduleCatLeftHomologyData.i n ≫
    Ideal.PowerSubmodule.inclusion I S.X₂ h

/-- The canonical middle-term map lands in the cycles of the shallower stage. -/
@[stacks 0G3K "canonical adic cycle map is a cycle"]
theorem cyclesStageToStageMiddle_comp_g
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    cyclesStageToStageMiddle S I h ≫ (stage S I m).g = 0 := sorry

/-- The canonical middle-term map agrees with the ambient cycle representative. -/
@[stacks 0G3K "canonical adic cycle map inclusion formula"]
theorem cyclesStageToStageMiddle_comp_subtype
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    cyclesStageToStageMiddle S I h ≫ (subtypeMap S I m).τ₂ =
      cyclesStageToMiddle S I n := sorry

/-- The canonical map from a deep ambient-cycle stage to the cycles of a shallower stage. -/
@[stacks 0G3K "canonical adic cycle map to shallower stage cycles"]
noncomputable def cyclesStageToStageCycles
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    cyclesStage S I n ⟶ (stage S I m).moduleCatLeftHomologyData.K :=
  (stage S I m).moduleCatLeftHomologyData.liftK
    (cyclesStageToStageMiddle S I h)
    (cyclesStageToStageMiddle_comp_g S I h)

/-- The canonical cycle lift has the expected middle-term representative. -/
@[stacks 0G3K "canonical adic cycle lift inclusion formula"]
theorem cyclesStageToStageCycles_comp_i
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    cyclesStageToStageCycles S I h ≫
        (stage S I m).moduleCatLeftHomologyData.i =
      cyclesStageToStageMiddle S I h := sorry

/-- The canonical cycle lift represents the original ambient middle-term element. -/
@[stacks 0G3K "canonical adic cycle lift representative formula"]
theorem cyclesStageToStageCycles_comp_toMiddle
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n) :
    cyclesStageToStageCycles S I h ≫ stageCyclesToMiddle S I m =
      cyclesStageToMiddle S I n := sorry

/-- A reverse comparison is the canonical quotient map on cycle representatives. -/
@[stacks 0G3K "canonical reverse comparison specification"]
def ReverseSpec
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n)
    (ψ : ambientStage S I n ⟶ homologyStage S I m) : Prop :=
  cyclesStageToAmbient S I n ≫ ψ =
    cyclesStageToStageCycles S I h ≫
      (stage S I m).moduleCatLeftHomologyData.π

/-- The morphism specification is equivalent to its formula on arbitrary cycle representatives. -/
@[stacks 0G3K "canonical reverse comparison specification equivalence"]
theorem reverseSpec_iff
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n)
    (ψ : ambientStage S I n ⟶ homologyStage S I m) :
    ReverseSpec S I h ψ ↔
      ∀ (x : cyclesStage S I n) (z : (stage S I m).moduleCatLeftHomologyData.K),
        (cyclesStageToMiddle S I n).hom x = (stageCyclesToMiddle S I m).hom z →
          ψ.hom ((cyclesStageToAmbient S I n).hom x) =
            (stage S I m).moduleCatLeftHomologyData.π.hom z := sorry

/-- A deeper ambient cycle stage has a representative among the cycles of a shallower stage. -/
@[stacks 0G3K "adic cycle representative in a shallower stage"]
theorem exists_stageCycle_of_le
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n)
    (x : cyclesStage S I n) :
    ∃ z : (stage S I m).moduleCatLeftHomologyData.K,
      (cyclesStageToMiddle S I n).hom x = (stageCyclesToMiddle S I m).hom z := sorry

/-- The representative specification uniquely determines a reverse comparison. -/
@[stacks 0G3K "uniqueness of the canonical reverse comparison"]
theorem reverse_ext
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) {m n : ℕ} (h : m ≤ n)
    {ψ ψ' : ambientStage S I n ⟶ homologyStage S I m}
    (hψ : ReverseSpec S I h ψ) (hψ' : ReverseSpec S I h ψ') :
    ψ = ψ' := sorry

/-- The source-faithful image bound in Lemma 15.102.1. -/
@[stacks 0G3K "eventual image bound for filtered homology"]
def ImageBound (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c n : ℕ) : Prop :=
  LinearMap.range (toAmbient S I n).hom ≤
    Ideal.PowerSubmodule.stage I S.moduleCatLeftHomologyData.H (n - c)

/-- The canonical map `I^n H → H_(n-c)` supplied by the comparison theorem. -/
@[stacks 0G3K "eventual reverse map for filtered homology"]
abbrev ReverseMap (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c n : ℕ) :=
  ambientStage S I n ⟶ homologyStage S I (n - c)

/-- The factor of `H_n → H` through `I^(n-c) H` used in the source statement. -/
@[stacks 0G3K "eventual forward factor for filtered homology"]
abbrev ForwardMap (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c n : ℕ) :=
  homologyStage S I n ⟶ ambientStage S I (n - c)

/-- The image bound puts every stage-homology class in the required ambient adic stage. -/
@[stacks 0G3K "image-bound membership for filtered homology"]
theorem toAmbient_mem_of_imageBound
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c n : ℕ)
    (h : ImageBound S I c n) (x : homologyStage S I n) :
    (toAmbient S I n).hom x ∈
      Ideal.PowerSubmodule.stage I S.moduleCatLeftHomologyData.H (n - c) := sorry

/-- The canonical forward factor obtained by restricting the codomain of `toAmbient`. -/
@[stacks 0G3K "canonical forward factor for filtered homology"]
noncomputable def forwardMap
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c n : ℕ)
    (h : ImageBound S I c n) : ForwardMap S I c n :=
  ModuleCat.ofHom <|
    (toAmbient S I n).hom.codRestrict
      (Ideal.PowerSubmodule.stage I S.moduleCatLeftHomologyData.H (n - c))
      (toAmbient_mem_of_imageBound S I c n h)

/-- Forgetting the codomain restriction recovers the ambient homology map. -/
@[stacks 0G3K "canonical forward factor inclusion formula"]
theorem forwardMap_comp_subtype
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c n : ℕ)
    (h : ImageBound S I c n) :
    forwardMap S I c n h ≫
        ModuleCat.ofHom
          (Ideal.PowerSubmodule.subtype I S.moduleCatLeftHomologyData.H (n - c)) =
      toAmbient S I n := sorry

/-- Arithmetic bounds used when both shifts are defined. -/
@[stacks 0G3K "two-shift arithmetic bounds"]
theorem twoShiftBounds (c n : ℕ) (h : 2 * c ≤ n) :
    c ≤ n ∧ c ≤ n - c ∧ n - c - c ≤ n := sorry

/-- A source-facing comparison with visible reverse maps and canonical forward factors. -/
@[stacks 0G3K "shifted adic homology comparison"]
structure Comparison (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ) where
  /-- The eventual image bound from which every forward factor is constructed. -/
  imageBound : ∀ (n : ℕ), c ≤ n → ImageBound S I c n
  /-- The canonical-direction maps `I^n H → H_(n-c)` on the stable range. -/
  reverse : ∀ (n : ℕ), c ≤ n → ReverseMap S I c n
  /-- Every reverse map is characterized by the canonical cycle-representative formula. -/
  reverse_spec : ∀ (n : ℕ) (h : c ≤ n),
    ReverseSpec S I (Nat.sub_le n c) (reverse n h)

namespace Comparison

/-! The shifted formulation is the reusable public surface.  The indexed `Comparison` structure
above remains as a source-facing bridge for statements which spell out `n - c` explicitly. -/

/-- Canonical reverse maps commute with adjacent transitions on the stable range. -/
@[stacks 0G3K "canonical reverse comparison naturality"]
theorem reverse_naturality
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) (n : ℕ) :
    let h := Nat.add_le_add_left (Nat.le_succ n) c
    ambientTransition S I h ≫ D.reverse (c + n) (Nat.le_add_right c n) =
      D.reverse (c + (n + 1)) (Nat.le_add_right c (n + 1)) ≫
        homologyTransition S I (Nat.sub_le_sub_right h c) := sorry

/-- A canonical reverse map followed by the forward factor is the ambient transition. -/
@[stacks 0G3K "canonical reverse-forward comparison"]
theorem reverse_forward
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) (n : ℕ) (h : 2 * c ≤ n) :
    (D.reverse n (twoShiftBounds c n h).1 : ambientStage S I n ⟶
        homologyStage S I (n - c)) ≫
        forwardMap S I c (n - c)
          (D.imageBound (n - c) (twoShiftBounds c n h).2.1) =
      ambientTransition S I (m := n - c - c) (n := n)
        (twoShiftBounds c n h).2.2 := sorry

/-- A canonical forward factor followed by the reverse map is the homology transition. -/
@[stacks 0G3K "canonical forward-reverse comparison"]
theorem forward_reverse
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) (n : ℕ) (h : 2 * c ≤ n) :
    (forwardMap S I c n (D.imageBound n (twoShiftBounds c n h).1) :
        homologyStage S I n ⟶ ambientStage S I (n - c)) ≫
        D.reverse (n - c) (twoShiftBounds c n h).2.1 =
      homologyTransition S I (twoShiftBounds c n h).2.2 := sorry

/-- A forward map of filtered homology after a fixed shift. -/
@[stacks 0G3K "forward shifted filtered-homology map"]
abbrev Shift (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ) :=
  (tower S I).shift c ⟶ ambientTower S I

/-- A reverse map after the same fixed shift. -/
@[stacks 0G3K "reverse shifted filtered-homology map"]
abbrev ReverseShift (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ) :=
  (ambientTower S I).shift c ⟶ tower S I

/-- The component of the shifted forward transformation determined by indexed comparison data. -/
@[stacks 0G3K "shifted filtered-homology forward component"]
noncomputable def forwardShiftApp
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) (n : ℕ) :
    ((tower S I).shift c).obj (Opposite.op n) ⟶ (ambientTower S I).obj (Opposite.op n) :=
  forwardMap S I c (c + n) (D.imageBound (c + n) (Nat.le_add_right c n)) ≫
    eqToHom (congrArg (ambientStage S I) (Nat.add_sub_cancel_left c n))

/-- The shifted forward components commute with successor transitions. -/
@[stacks 0G3K "shifted filtered-homology forward naturality"]
theorem forwardShiftApp_naturality
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) (n : ℕ) :
    ((tower S I).shift c).stepMap n ≫ forwardShiftApp D n =
      forwardShiftApp D (n + 1) ≫ (ambientTower S I).stepMap n := sorry

/-- The shifted forward natural transformation determined by indexed comparison data. -/
@[stacks 0G3K "canonical shifted filtered-homology forward map"]
noncomputable def forwardShift
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) : Shift S I c :=
  NatTrans.ofOpSequence (forwardShiftApp D) (forwardShiftApp_naturality D)

/-- Evaluation of the shifted forward natural transformation. -/
@[simp, stacks 0G3K "canonical shifted filtered-homology forward evaluation"]
theorem forwardShift_app
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) (n : ℕ) :
    D.forwardShift.app (Opposite.op n) = forwardShiftApp D n := sorry

/-- The component of the shifted reverse transformation determined by indexed comparison data. -/
@[stacks 0G3K "shifted filtered-homology reverse component"]
noncomputable def reverseShiftApp
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) (n : ℕ) :
    ((ambientTower S I).shift c).obj (Opposite.op n) ⟶ (tower S I).obj (Opposite.op n) :=
  D.reverse (c + n) (Nat.le_add_right c n) ≫
    eqToHom (congrArg (homologyStage S I) (Nat.add_sub_cancel_left c n))

/-- The shifted reverse components commute with successor transitions. -/
@[stacks 0G3K "shifted filtered-homology reverse naturality"]
theorem reverseShiftApp_naturality
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) (n : ℕ) :
    ((ambientTower S I).shift c).stepMap n ≫ reverseShiftApp D n =
      reverseShiftApp D (n + 1) ≫ (tower S I).stepMap n := sorry

/-- The shifted reverse natural transformation determined by indexed comparison data. -/
@[stacks 0G3K "canonical shifted filtered-homology reverse map"]
noncomputable def reverseShift
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) : ReverseShift S I c :=
  NatTrans.ofOpSequence (reverseShiftApp D) (reverseShiftApp_naturality D)

/-- Evaluation of the shifted reverse natural transformation. -/
@[simp, stacks 0G3K "canonical shifted filtered-homology reverse evaluation"]
theorem reverseShift_app
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) (n : ℕ) :
    D.reverseShift.app (Opposite.op n) = reverseShiftApp D n := sorry

/-- The source-facing ambient factorization for a shifted forward map. -/
@[stacks 0G3K "shifted filtered-homology forward specification"]
def ForwardSpec (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ)
    (α : Shift S I c) : Prop :=
  ∀ n : ℕ,
    α.app (Opposite.op n) ≫
        ModuleCat.ofHom
          (Ideal.PowerSubmodule.subtype I S.moduleCatLeftHomologyData.H n) =
      toAmbient S I (c + n)

/-- A shifted reverse transformation is canonical on every adic cycle representative. -/
@[stacks 0G3K "shifted filtered-homology reverse specification"]
def ReverseShiftSpec (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ)
    (β : ReverseShift S I c) : Prop :=
  ∀ n : ℕ,
    ReverseSpec S I (Nat.le_add_left n c) (β.app (Opposite.op n))

/-- A shifted pair consists of pro-level inverse maps with canonical forward and reverse maps. -/
@[stacks 0G3K "shifted filtered-homology comparison predicate"]
def IsComparison (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ)
    (α : Shift S I c) (β : ReverseShift S I c) : Prop :=
  Pro.SequentialHom.IsShiftedInverse c c α β ∧
    ForwardSpec S I c α ∧ ReverseShiftSpec S I c β

/-- The canonical shifted forward map satisfies the ambient factorization and image conditions. -/
@[stacks 0G3K "indexed comparison forward specification"]
theorem forwardShift_spec
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) : ForwardSpec S I c D.forwardShift := sorry

/-- The shifted reverse map from indexed comparison data is canonical. -/
@[stacks 0G3K "indexed comparison reverse specification"]
theorem reverseShift_spec
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) : ReverseShiftSpec S I c D.reverseShift := sorry

/-- A shifted ambient factorization implies the corresponding image containment. -/
@[stacks 0G3K "shifted factorization image bound"]
theorem range_le_of_forwardSpec
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ)
    (α : Shift S I c) (hα : ForwardSpec S I c α) (n : ℕ) :
    LinearMap.range (toAmbient S I (c + n)).hom ≤
      Ideal.PowerSubmodule.stage I S.moduleCatLeftHomologyData.H n := sorry

/-- The canonical shifted maps attached to indexed comparison data are mutually inverse up to
the two-shift transition maps. -/
@[stacks 0G3K "indexed comparison shifted inverse"]
theorem forwardShift_isShiftedInverse
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) :
    Pro.SequentialHom.IsShiftedInverse c c D.forwardShift D.reverseShift := sorry

/-- Indexed comparison data canonically determines a shifted comparison. -/
@[stacks 0G3K "indexed comparison to shifted comparison"]
theorem isComparison
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) : IsComparison S I c D.forwardShift D.reverseShift := sorry

/-- The pro-morphism represented by a shifted forward map. -/
@[stacks 0G3K "filtered-homology pro-morphism"]
noncomputable def proMap (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ)
    (α : Shift S I c) :
    (Pro.lim (C := ModuleCat.{v} A) ℕᵒᵖ).obj (tower S I) ⟶
      (Pro.lim (C := ModuleCat.{v} A) ℕᵒᵖ).obj (ambientTower S I) :=
  (Pro.SequentialHom.ofShiftNatTrans c α).toHom

/-- The reverse pro-morphism represented by a shifted reverse map. -/
@[stacks 0G3K "reverse filtered-homology pro-morphism"]
noncomputable def proReverseMap
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ)
    (β : ReverseShift S I c) :
    (Pro.lim (C := ModuleCat.{v} A) ℕᵒᵖ).obj (ambientTower S I) ⟶
      (Pro.lim (C := ModuleCat.{v} A) ℕᵒᵖ).obj (tower S I) :=
  (Pro.SequentialHom.ofShiftNatTrans c β).toHom

/-- Indexed comparison data determines an explicit isomorphism of the two pro-objects. -/
@[stacks 0G3K "indexed filtered-homology pro-isomorphism data"]
noncomputable abbrev toProIso
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) :
    (Pro.lim (C := ModuleCat.{v} A) ℕᵒᵖ).obj (tower S I) ≅
      (Pro.lim (C := ModuleCat.{v} A) ℕᵒᵖ).obj (ambientTower S I) :=
  D.isComparison.1.iso

/-- The forward map of the canonical pro-isomorphism is the shifted comparison map. -/
@[simp, stacks 0G3K "indexed filtered-homology pro-isomorphism forward map"]
theorem toProIso_hom
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) : D.toProIso.hom = proMap S I c D.forwardShift := sorry

/-- The inverse map of the canonical pro-isomorphism is the shifted reverse comparison map. -/
@[simp, stacks 0G3K "indexed filtered-homology pro-isomorphism inverse map"]
theorem toProIso_inv
    {S : ShortComplex (ModuleCat.{v} A)} {I : Ideal A} {c : ℕ}
    (D : Comparison S I c) :
    D.toProIso.inv = proReverseMap S I c D.reverseShift := sorry

/-- The shifted image condition implies the source-indexed `n - c` bound. -/
@[stacks 0G3K "shifted image bound bridge"]
theorem imageBound_of_forwardSpec
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A) (c : ℕ)
    (α : Shift S I c) (hα : ForwardSpec S I c α)
    {n : ℕ} (hn : c ≤ n) : ImageBound S I c n := sorry

/-- The reusable shifted comparison theorem only needs finiteness of the middle term. -/
@[stacks 0G3K "shifted filtered-homology comparison from a finite middle term"]
theorem existsShiftedComparison_of_finite_middle [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A)
    [Module.Finite A (S.X₂ : Type v)] :
    ∃ c : ℕ, 0 < c ∧ ∃ α : Shift S I c, ∃ β : ReverseShift S I c,
      IsComparison S I c α β := sorry

/-- The source-faithful existence theorem with explicit shifted natural transformations. -/
@[stacks 0G3K "Lemma 15.102.1 shifted comparison data"]
theorem existsShiftedComparison [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A)
    [Module.Finite A (S.X₁ : Type v)] [Module.Finite A (S.X₂ : Type v)]
    [Module.Finite A (S.X₃ : Type v)] :
    ∃ c : ℕ, 0 < c ∧ ∃ α : Shift S I c, ∃ β : ReverseShift S I c,
      IsComparison S I c α β := sorry

end Comparison

/-- The reusable Artin--Rees comparison only needs finiteness of the middle term. -/
@[stacks 0G3K "filtered-homology comparison from a finite middle term"]
theorem existsComparison_of_finite_middle [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A)
    [Module.Finite A (S.X₂ : Type v)] :
    ∃ c : ℕ, ∃ D : Comparison S I c, 0 < c := sorry

/-- The exact source-facing existence statement for Lemma 15.102.1. -/
@[stacks 0G3K "Lemma 15.102.1 shifted comparison"]
theorem existsComparison [IsNoetherianRing A]
    (S : ShortComplex (ModuleCat.{v} A)) (I : Ideal A)
    [Module.Finite A (S.X₁ : Type v)] [Module.Finite A (S.X₂ : Type v)]
    [Module.Finite A (S.X₃ : Type v)] :
    ∃ c : ℕ, ∃ D : Comparison S I c, 0 < c := sorry

end CategoryTheory.ShortComplex.IdealPower.Submodule
