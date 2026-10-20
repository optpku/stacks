/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Sections
public import ReasLib.RingTheory.AdicCompletion.QuotientSystem
import StacksCheckRecall

/-!
# Lemma 10.96.5: positive-stage inverse systems

@stack 0318
-/

@[expose] public section

universe u

noncomputable section

open AdicCompletion
open CategoryTheory
open CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

-- Local declaration justification: this abbreviation fixes the indexing and module universe for
-- the concrete inverse systems below without adding a public alias.
local notation "ModuleInverseSystem" => OrderDual ℕ+ ⥤ ModuleCat R

/-- Helper for Lemma 10.96.5: the quotient-stage map
`M^∧ / I ^ n M^∧ → M / I ^ n M` induced by the evaluation map at stage `n`. -/
abbrev ker_eval_quotient_stageMap (n : ℕ+) :
    (AdicCompletion I M ⧸ I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M))) →ₗ[R]
      M ⧸ (I ^ (n : ℕ) • (⊤ : Submodule R M)) :=
  Submodule.liftQ _ (AdicCompletion.eval I M (n : ℕ))
    (AdicCompletion.pow_smul_top_le_ker_eval (I := I) (M := M) (n := n))

/-- Helper for Lemma 10.96.5: a readable name for the positive stage corresponding to an object of
`OrderDual ℕ+`. -/
abbrev stagePNat (i : OrderDual ℕ+) : ℕ+ :=
  OrderDual.ofDual i

/-- Helper for Lemma 10.96.5: the positive-stage inverse system
`M^∧ / I ^ n M^∧`. -/
noncomputable abbrev positive_stage_completion_system : ModuleInverseSystem :=
  AdicCompletion.positiveQuotientSystem I (AdicCompletion I M)

/-- Helper for Lemma 10.96.5: the positive-stage inverse system `M / I ^ n M`. -/
noncomputable abbrev positive_stage_module_system : ModuleInverseSystem :=
  AdicCompletion.positiveQuotientSystem I M

/-- Helper for Lemma 10.96.5: an arbitrary positive-stage completion transition map preserves the
left kernels `K_n / I ^ n M^∧`. -/
lemma positive_stage_completion_map_mem_kernel {i j : OrderDual ℕ+} (f : i ⟶ j)
    {x : AdicCompletion I M ⧸
      I ^ ((stagePNat i : ℕ)) • (⊤ : Submodule R (AdicCompletion I M))}
    (hx : x ∈ LinearMap.ker
      (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i))) :
    ((AdicCompletion.positiveQuotientSystem I (AdicCompletion I M)).map f).hom x ∈
      LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat j)) := sorry

/-- The component map of the left-kernel inverse system at an arbitrary stage morphism. -/
noncomputable abbrev positive_stage_left_system_map {i j : OrderDual ℕ+} (f : i ⟶ j) :
    ModuleCat.of R
        (LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i))) ⟶
      ModuleCat.of R
        (LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat j))) :=
  ModuleCat.ofHom <|
    (((AdicCompletion.positiveQuotientSystem I (AdicCompletion I M)).map f).hom.domRestrict
        (LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i)))).codRestrict
      (LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat j)))
      (fun x ↦ positive_stage_completion_map_mem_kernel (I := I) (M := M) f x.2)

/-- The left-kernel component at an identity stage morphism is the identity map. -/
lemma positive_stage_left_system_map_id (i : OrderDual ℕ+) :
    positive_stage_left_system_map (R := R) (I := I) (M := M) (𝟙 i) = 𝟙 _ := sorry

/-- The left-kernel component maps respect composition of stage morphisms. -/
lemma positive_stage_left_system_map_comp
    {i j k : OrderDual ℕ+} (f : i ⟶ j) (g : j ⟶ k) :
    positive_stage_left_system_map (R := R) (I := I) (M := M) (f ≫ g) =
      positive_stage_left_system_map (R := R) (I := I) (M := M) f ≫
        positive_stage_left_system_map (R := R) (I := I) (M := M) g := sorry

/-- Helper for Lemma 10.96.5: the positive-stage inverse system
`K_n / I ^ n M^∧` cut out inside the completion-quotient system. -/
noncomputable abbrev positive_stage_left_system
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] : ModuleInverseSystem where
  obj i := ModuleCat.of R
    (LinearMap.ker (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i)))
  map := fun {_ _} f ↦ positive_stage_left_system_map (R := R) (I := I) (M := M) f
  map_id := positive_stage_left_system_map_id (R := R) (I := I) (M := M)
  map_comp := positive_stage_left_system_map_comp (R := R) (I := I) (M := M)

/-- Helper for Lemma 10.96.5: once the inverse limit of the quotient kernels vanishes, the source
kernel equality `K_n = I ^ n M^∧` follows at each positive stage. -/
lemma ker_eval_eq_pow_smul_top_of_left_limit_isZero
    (hzero : IsZero (limit (positive_stage_left_system (R := R) (I := I) (M := M))))
    (n : ℕ+) :
    (eval I M (n : ℕ)).ker =
      I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)) := sorry

/-- The stage component of the inclusion from the left-kernel system into the completion
quotient system. -/
abbrev positive_stage_left_ι_app (i : OrderDual ℕ+) :
    (positive_stage_left_system (R := R) (I := I) (M := M)).obj i ⟶
      (positive_stage_completion_system (R := R) (I := I) (M := M)).obj i :=
  ModuleCat.ofHom
    (LinearMap.ker
      (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i))).subtype

/-- The left-kernel inclusions commute with every positive-stage transition. -/
lemma positive_stage_left_ι_naturality
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    (positive_stage_left_system (R := R) (I := I) (M := M)).map f ≫
        positive_stage_left_ι_app (R := R) (I := I) (M := M) j =
      positive_stage_left_ι_app (R := R) (I := I) (M := M) i ≫
        (positive_stage_completion_system (R := R) (I := I) (M := M)).map f := sorry

/-- Helper for Lemma 10.96.5: the kernel inclusion
`K_n / I ^ n M^∧ → M^∧ / I ^ n M^∧` as a map of inverse systems. -/
noncomputable abbrev positive_stage_left_ι :
    (positive_stage_left_system (R := R) (I := I) (M := M)) ⟶
      (positive_stage_completion_system (R := R) (I := I) (M := M)) where
  app i := positive_stage_left_ι_app (R := R) (I := I) (M := M) i
  naturality := fun {X Y} f ↦
    positive_stage_left_ι_naturality (R := R) (I := I) (M := M) (i := X) (j := Y) f

/-- The stage component of the quotient map from completion quotients to module quotients. -/
abbrev positive_stage_stageMap_app (i : OrderDual ℕ+) :
    (positive_stage_completion_system (R := R) (I := I) (M := M)).obj i ⟶
      (positive_stage_module_system (R := R) (I := I) (M := M)).obj i :=
  ModuleCat.ofHom (ker_eval_quotient_stageMap (I := I) (M := M) (stagePNat i))

/-- The stage quotient maps commute with every positive-stage transition. -/
lemma positive_stage_stageMap_naturality
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    (positive_stage_completion_system (R := R) (I := I) (M := M)).map f ≫
        positive_stage_stageMap_app (R := R) (I := I) (M := M) j =
      positive_stage_stageMap_app (R := R) (I := I) (M := M) i ≫
        (positive_stage_module_system (R := R) (I := I) (M := M)).map f := sorry

/-- Helper for Lemma 10.96.5: the stagewise quotient map
`M^∧ / I ^ n M^∧ → M / I ^ n M` as a map of inverse systems. -/
noncomputable abbrev positive_stage_stageMap :
    (positive_stage_completion_system (R := R) (I := I) (M := M)) ⟶
      (positive_stage_module_system (R := R) (I := I) (M := M)) where
  app i := positive_stage_stageMap_app (R := R) (I := I) (M := M) i
  naturality := fun {X Y} f ↦
    positive_stage_stageMap_naturality (R := R) (I := I) (M := M) (i := X) (j := Y) f

/-- The kernel inclusion followed by the stage quotient map is the zero natural transformation. -/
lemma positive_stage_left_ι_comp_stageMap :
    positive_stage_left_ι (R := R) (I := I) (M := M) ≫
      positive_stage_stageMap (R := R) (I := I) (M := M) = 0 := sorry

/-- Helper for Lemma 10.96.5: the source-proof short complex of positive-stage inverse systems
`0 → K_n / I ^ n M^∧ → M^∧ / I ^ n M^∧ → M / I ^ n M → 0`. -/
noncomputable abbrev positive_stage_shortComplex : ShortComplex ModuleInverseSystem :=
  ShortComplex.mk
    (positive_stage_left_ι (R := R) (I := I) (M := M))
    (positive_stage_stageMap (R := R) (I := I) (M := M))
    (positive_stage_left_ι_comp_stageMap (R := R) (I := I) (M := M))

/-- Helper for Lemma 10.96.5: the positive-stage short complex of inverse systems is short exact,
because each evaluation is exactly the quotient-stage kernel short exact sequence. -/
lemma positive_stage_quotient_system_shortExact :
    (positive_stage_shortComplex (R := R) (I := I) (M := M)).ShortExact := sorry


/- Positive-stage system data and properties retained for Lemma 10.96.5. -/
@[stacks 0318 "quotient stage map"]
#check @ker_eval_quotient_stageMap
@[stacks 0318 "surjectivity of completion evaluation"]
#check @AdicCompletion.eval_surjective
@[stacks 0318 "kernel short complex of a surjective linear map"]
#check @LinearMap.shortExact_shortComplexKer
@[stacks 0318 "positive adic quotient transition"]
#check @AdicCompletion.positiveQuotientStepMap
@[stacks 0318 "completion inverse system"]
#check @positive_stage_completion_system
@[stacks 0318 "module inverse system"]
#check @positive_stage_module_system
@[stacks 0318 "left kernel inverse system"]
#check @positive_stage_left_system
@[stacks 0318 "left kernel system transition"]
#check @positive_stage_left_system_map
@[stacks 0318 "identity law for left kernel transitions"]
#check @positive_stage_left_system_map_id
@[stacks 0318 "composition law for left kernel transitions"]
#check @positive_stage_left_system_map_comp
@[stacks 0318 "Mittag-Leffler criterion from surjective transitions"]
#check @Functor.isMittagLeffler_of_surjective
@[stacks 0318 "completion kernel criterion"]
#check @ker_eval_eq_pow_smul_top_of_left_limit_isZero
@[stacks 0318 "left system inclusion"]
#check @positive_stage_left_ι
@[stacks 0318 "left system inclusion component"]
#check @positive_stage_left_ι_app
@[stacks 0318 "naturality of the left system inclusion"]
#check @positive_stage_left_ι_naturality
@[stacks 0318 "stage quotient map"]
#check @positive_stage_stageMap
@[stacks 0318 "stage quotient component"]
#check @positive_stage_stageMap_app
@[stacks 0318 "naturality of the stage quotient map"]
#check @positive_stage_stageMap_naturality
@[stacks 0318 "zero composite of the kernel inclusion and quotient map"]
#check @positive_stage_left_ι_comp_stageMap
@[stacks 0318 "positive-stage short complex"]
#check @positive_stage_shortComplex
@[stacks 0318 "positive-stage short exactness"]
#check @positive_stage_quotient_system_shortExact

/- The computational fields below are explicit. Any `sorryAx` reported here is confined to the
canonical quotient-system laws or to the named functoriality, naturality, and zero-composite
proof obligations above. -/
#print axioms positive_stage_completion_system
#print axioms positive_stage_module_system
#print axioms positive_stage_left_system
#print axioms positive_stage_left_ι
#print axioms positive_stage_stageMap
#print axioms positive_stage_shortComplex

end
