/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap10.Lemma_10_96_5.StageSystems
import StacksCheckRecall

@[expose] public section

/-!
Positive-stage inverse-limit support for Lemma 10.96.5.
@stack 0318
-/

universe u

noncomputable section

open AdicCompletion
open CategoryTheory
open CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Helper for Lemma 10.96.5: extend a cone on the positive-stage system `M / I ^ n M` by the
trivial zeroth stage. -/
noncomputable def positive_stage_module_family
    (s : Cone (positive_stage_module_system (R := R) (I := I) (M := M))) (n : ℕ) :
    s.pt →ₗ[R] (M ⧸ I ^ n • (⊤ : Submodule R M)) :=
  if hn : 0 < n then
    (s.π.app (OrderDual.toDual ⟨n, hn⟩)).hom
  else
    0

/-- Helper for Lemma 10.96.5: the extended positive-stage module family satisfies the full
compatibility relations defining the adic completion of `M`. -/
theorem positive_stage_module_family_compat
    (s : Cone (positive_stage_module_system (R := R) (I := I) (M := M)))
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I M hmn ∘ₗ
        positive_stage_module_family (R := R) (I := I) (M := M) s n =
      positive_stage_module_family (R := R) (I := I) (M := M) s m := sorry

/-- Helper for Lemma 10.96.5: on a positive stage, the extended module family is the original
cone leg. -/
theorem positive_stage_module_family_pnat
    (s : Cone (positive_stage_module_system (R := R) (I := I) (M := M))) (n : ℕ+) :
    positive_stage_module_family (R := R) (I := I) (M := M) s (n : ℕ) =
      (s.π.app (OrderDual.toDual n)).hom := sorry

/-- Helper for Lemma 10.96.5: the evaluation maps on `AdicCompletion I M` define a cone on the
positive-stage inverse system `M / I ^ n M`. -/
theorem positive_stage_module_completion_cone_naturality
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    ((Functor.const (OrderDual ℕ+)).obj (ModuleCat.of R (AdicCompletion I M))).map f ≫
      ModuleCat.ofHom (AdicCompletion.eval I M ((stagePNat j : ℕ))) =
        ModuleCat.ofHom (AdicCompletion.eval I M ((stagePNat i : ℕ))) ≫
          (positive_stage_module_system (R := R) (I := I) (M := M)).map f := sorry

/-- Helper for Lemma 10.96.5: the completion of `M` maps to the positive-stage quotient system
via its evaluation maps. -/
noncomputable abbrev positive_stage_module_completion_cone :
    Cone (positive_stage_module_system (R := R) (I := I) (M := M)) :=
  { pt := ModuleCat.of R (AdicCompletion I M)
    π :=
      { app := fun i ↦ ModuleCat.ofHom (AdicCompletion.eval I M ((stagePNat i : ℕ)))
        naturality := fun {_ _} f ↦
          positive_stage_module_completion_cone_naturality (R := R) (I := I) (M := M) f } }

/-- Helper for Lemma 10.96.5: maps into `AdicCompletion I M` are determined by all positive-stage
evaluation maps. -/
theorem positive_stage_module_completion_hom_ext
    {X : ModuleCat R}
    {f g : X ⟶ (positive_stage_module_completion_cone (R := R) (I := I) (M := M)).pt}
    (hfg :
      ∀ n : ℕ+,
        f ≫ (positive_stage_module_completion_cone (R := R) (I := I) (M := M)).π.app
            (OrderDual.toDual n) =
          g ≫ (positive_stage_module_completion_cone (R := R) (I := I) (M := M)).π.app
            (OrderDual.toDual n)) :
    f = g := sorry

/-- Helper for Lemma 10.96.5: the universal lift from a cone on the positive-stage module system
to the completion of `M`. -/
noncomputable abbrev positive_stage_module_completion_lift
    (s : Cone (positive_stage_module_system (R := R) (I := I) (M := M))) :
    s.pt ⟶ ModuleCat.of R (AdicCompletion I M) :=
  ModuleCat.ofHom
    (AdicCompletion.lift I
      (positive_stage_module_family (R := R) (I := I) (M := M) s)
      (positive_stage_module_family_compat (R := R) (I := I) (M := M) s))

/-- Helper for Lemma 10.96.5: the universal lift to the completion of `M` has the expected
positive-stage formula. -/
theorem positive_stage_module_completion_lift_fac :
    ∀ (s : Cone (positive_stage_module_system (R := R) (I := I) (M := M)))
      (i : OrderDual ℕ+),
      positive_stage_module_completion_lift (R := R) (I := I) (M := M) s ≫
          (positive_stage_module_completion_cone (R := R) (I := I) (M := M)).π.app i =
        s.π.app i := sorry

/-- Helper for Lemma 10.96.5: the completion lift is uniquely determined by its positive-stage
evaluations. -/
theorem positive_stage_module_completion_lift_uniq :
    ∀ (s : Cone (positive_stage_module_system (R := R) (I := I) (M := M)))
      (m : s.pt ⟶ (positive_stage_module_completion_cone (R := R) (I := I) (M := M)).pt),
      (∀ i,
          m ≫ (positive_stage_module_completion_cone (R := R) (I := I) (M := M)).π.app i =
            s.π.app i) →
        m = positive_stage_module_completion_lift (R := R) (I := I) (M := M) s := sorry

/-- Helper for Lemma 10.96.5: the evaluation cone from `AdicCompletion I M` is limiting for the
positive-stage system `M / I ^ n M`. -/
noncomputable def positive_stage_module_completion_isLimit :
    IsLimit (positive_stage_module_completion_cone (R := R) (I := I) (M := M)) where
  lift := positive_stage_module_completion_lift (R := R) (I := I) (M := M)
  fac := positive_stage_module_completion_lift_fac (R := R) (I := I) (M := M)
  uniq := positive_stage_module_completion_lift_uniq (R := R) (I := I) (M := M)

/-- Helper for Lemma 10.96.5: the positive-stage system `M / I ^ n M` has inverse limit
`AdicCompletion I M`. -/
noncomputable abbrev positive_stage_module_completion_limitCone :
    LimitCone (positive_stage_module_system (R := R) (I := I) (M := M)) :=
  { cone := positive_stage_module_completion_cone (R := R) (I := I) (M := M)
    isLimit := positive_stage_module_completion_isLimit (R := R) (I := I) (M := M) }

/-- Helper for Lemma 10.96.5: the positive-stage inverse limit `lim_n M / I ^ n M` is canonically
identified with `AdicCompletion I M`. -/
noncomputable abbrev positive_stage_module_system_limit_iso :
    limit (positive_stage_module_system (R := R) (I := I) (M := M)) ≅
      ModuleCat.of R (AdicCompletion I M) :=
  limit.isoLimitCone (positive_stage_module_completion_limitCone (R := R) (I := I) (M := M))

/-- Helper for Lemma 10.96.5: the inverse of the positive-stage module limit identification
evaluates to the canonical completion projection at each stage. -/
theorem positive_stage_module_system_limit_iso_inv_π (i : OrderDual ℕ+) :
    (positive_stage_module_system_limit_iso (R := R) (I := I) (M := M)).inv ≫
        limit.π (positive_stage_module_system (R := R) (I := I) (M := M)) i =
      ModuleCat.ofHom (AdicCompletion.eval I M ((stagePNat i : ℕ))) := sorry

/-- Helper for Lemma 10.96.5: the forward positive-stage module limit identification has the
expected stage projection formula. -/
theorem positive_stage_module_system_limit_iso_hom_π (i : OrderDual ℕ+) :
    (positive_stage_module_system_limit_iso (R := R) (I := I) (M := M)).hom ≫
        ModuleCat.ofHom (AdicCompletion.eval I M ((stagePNat i : ℕ))) =
      limit.π (positive_stage_module_system (R := R) (I := I) (M := M)) i := sorry

/-- Helper for Lemma 10.96.5: extend a cone on the positive-stage system
`M^∧ / I ^ n M^∧` by the trivial zeroth stage. -/
noncomputable def positive_stage_completion_family
    (s : Cone (positive_stage_completion_system (R := R) (I := I) (M := M))) (n : ℕ) :
    s.pt →ₗ[R]
      (AdicCompletion I M ⧸ I ^ n • (⊤ : Submodule R (AdicCompletion I M))) :=
  if hn : 0 < n then
    (s.π.app (OrderDual.toDual ⟨n, hn⟩)).hom
  else
    0

/-- Helper for Lemma 10.96.5: the extended positive-stage completion family satisfies the full
compatibility relations defining the adic completion of `AdicCompletion I M`. -/
theorem positive_stage_completion_family_compat
    (s : Cone (positive_stage_completion_system (R := R) (I := I) (M := M)))
    {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I (AdicCompletion I M) hmn ∘ₗ
        positive_stage_completion_family (R := R) (I := I) (M := M) s n =
      positive_stage_completion_family (R := R) (I := I) (M := M) s m := sorry

/-- Helper for Lemma 10.96.5: on a positive stage, the extended completion family is the original
cone leg. -/
theorem positive_stage_completion_family_pnat
    (s : Cone (positive_stage_completion_system (R := R) (I := I) (M := M))) (n : ℕ+) :
    positive_stage_completion_family (R := R) (I := I) (M := M) s (n : ℕ) =
      (s.π.app (OrderDual.toDual n)).hom := sorry

/-- Helper for Lemma 10.96.5: the evaluation maps on `(AdicCompletion I M)^∧` define a cone on
the positive-stage inverse system `M^∧ / I ^ n M^∧`. -/
theorem positive_stage_completion_completion_cone_naturality
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    ((Functor.const (OrderDual ℕ+)).obj
        (ModuleCat.of R (AdicCompletion I (AdicCompletion I M)))).map f ≫
      ModuleCat.ofHom (AdicCompletion.eval I (AdicCompletion I M) ((stagePNat j : ℕ))) =
        ModuleCat.ofHom (AdicCompletion.eval I (AdicCompletion I M) ((stagePNat i : ℕ))) ≫
          (positive_stage_completion_system (R := R) (I := I) (M := M)).map f := sorry

/-- Helper for Lemma 10.96.5: the completion of `AdicCompletion I M` maps to the positive-stage
quotient system of `AdicCompletion I M` via its evaluation maps. -/
noncomputable abbrev positive_stage_completion_completion_cone :
    Cone (positive_stage_completion_system (R := R) (I := I) (M := M)) :=
  { pt := ModuleCat.of R (AdicCompletion I (AdicCompletion I M))
    π :=
      { app := fun i ↦
          ModuleCat.ofHom (AdicCompletion.eval I (AdicCompletion I M) ((stagePNat i : ℕ)))
        naturality := fun {_ _} f ↦
          positive_stage_completion_completion_cone_naturality
            (R := R) (I := I) (M := M) f } }

/-- Helper for Lemma 10.96.5: maps into `(AdicCompletion I M)^∧` are determined by all
positive-stage evaluations. -/
theorem positive_stage_completion_completion_hom_ext
    {X : ModuleCat R}
    {f g : X ⟶ (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)).pt}
    (hfg :
      ∀ n : ℕ+,
        f ≫ (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)).π.app
            (OrderDual.toDual n) =
          g ≫ (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)).π.app
            (OrderDual.toDual n)) :
    f = g := sorry

/-- Helper for Lemma 10.96.5: the universal lift from a cone on the positive-stage completion
system to the completion of `AdicCompletion I M`. -/
noncomputable abbrev positive_stage_completion_completion_lift
    (s : Cone (positive_stage_completion_system (R := R) (I := I) (M := M))) :
    s.pt ⟶ ModuleCat.of R (AdicCompletion I (AdicCompletion I M)) :=
  ModuleCat.ofHom
    (AdicCompletion.lift I
      (positive_stage_completion_family (R := R) (I := I) (M := M) s)
      (positive_stage_completion_family_compat (R := R) (I := I) (M := M) s))

/-- Helper for Lemma 10.96.5: the universal lift to the completion of `AdicCompletion I M` has
the expected positive-stage formula. -/
theorem positive_stage_completion_completion_lift_fac :
    ∀ (s : Cone (positive_stage_completion_system (R := R) (I := I) (M := M)))
      (i : OrderDual ℕ+),
      positive_stage_completion_completion_lift (R := R) (I := I) (M := M) s ≫
          (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)).π.app i =
        s.π.app i := sorry

/-- Helper for Lemma 10.96.5: the completion lift is uniquely determined by its positive-stage
evaluations. -/
theorem positive_stage_completion_completion_lift_uniq :
    ∀ (s : Cone (positive_stage_completion_system (R := R) (I := I) (M := M)))
      (m : s.pt ⟶
        (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)).pt),
      (∀ i,
          m ≫ (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)).π.app i =
            s.π.app i) →
        m = positive_stage_completion_completion_lift (R := R) (I := I) (M := M) s := sorry

/-- Helper for Lemma 10.96.5: the evaluation cone from `(AdicCompletion I M)^∧` is limiting for
the positive-stage system `M^∧ / I ^ n M^∧`. -/
noncomputable def positive_stage_completion_completion_isLimit :
    IsLimit (positive_stage_completion_completion_cone (R := R) (I := I) (M := M)) where
  lift := positive_stage_completion_completion_lift (R := R) (I := I) (M := M)
  fac := positive_stage_completion_completion_lift_fac (R := R) (I := I) (M := M)
  uniq := positive_stage_completion_completion_lift_uniq (R := R) (I := I) (M := M)

/-- Helper for Lemma 10.96.5: the positive-stage system `M^∧ / I ^ n M^∧` has inverse limit
`(AdicCompletion I M)^∧`. -/
noncomputable abbrev positive_stage_completion_completion_limitCone :
    LimitCone (positive_stage_completion_system (R := R) (I := I) (M := M)) :=
  { cone := positive_stage_completion_completion_cone (R := R) (I := I) (M := M)
    isLimit := positive_stage_completion_completion_isLimit (R := R) (I := I) (M := M) }

/-- Helper for Lemma 10.96.5: the positive-stage inverse limit `lim_n M^∧ / I ^ n M^∧` is
canonically identified with `(AdicCompletion I M)^∧`. -/
noncomputable abbrev positive_stage_completion_system_limit_iso :
    limit (positive_stage_completion_system (R := R) (I := I) (M := M)) ≅
      ModuleCat.of R (AdicCompletion I (AdicCompletion I M)) :=
  limit.isoLimitCone
    (positive_stage_completion_completion_limitCone (R := R) (I := I) (M := M))

/-- Helper for Lemma 10.96.5: the inverse of the positive-stage completion limit identification
evaluates to the canonical completion quotient map at each stage. -/
theorem positive_stage_completion_system_limit_iso_inv_π (i : OrderDual ℕ+) :
    (positive_stage_completion_system_limit_iso (R := R) (I := I) (M := M)).inv ≫
        limit.π (positive_stage_completion_system (R := R) (I := I) (M := M)) i =
      ModuleCat.ofHom (AdicCompletion.eval I (AdicCompletion I M) ((stagePNat i : ℕ))) := sorry

/-- Helper for Lemma 10.96.5: the forward positive-stage completion limit identification has the
expected stage projection formula. -/
theorem positive_stage_completion_system_limit_iso_hom_π (i : OrderDual ℕ+) :
    (positive_stage_completion_system_limit_iso (R := R) (I := I) (M := M)).hom ≫
        ModuleCat.ofHom (AdicCompletion.eval I (AdicCompletion I M) ((stagePNat i : ℕ))) =
      limit.π (positive_stage_completion_system (R := R) (I := I) (M := M)) i := sorry

@[stacks 0318 "positive-stage module family"]
#check @positive_stage_module_family
@[stacks 0318 "positive-stage module compatibility"]
#check @positive_stage_module_family_compat
@[stacks 0318 "positive-stage module family at positive stages"]
#check @positive_stage_module_family_pnat
@[stacks 0318 "positive-stage module completion cone"]
#check @positive_stage_module_completion_cone
@[stacks 0318 "positive-stage module cone naturality"]
#check @positive_stage_module_completion_cone_naturality
@[stacks 0318 "positive-stage module hom extensionality"]
#check @positive_stage_module_completion_hom_ext
@[stacks 0318 "positive-stage module completion lift"]
#check @positive_stage_module_completion_lift
@[stacks 0318 "positive-stage module lift factorization"]
#check @positive_stage_module_completion_lift_fac
@[stacks 0318 "positive-stage module lift uniqueness"]
#check @positive_stage_module_completion_lift_uniq
@[stacks 0318 "positive-stage module completion limit"]
#check @positive_stage_module_completion_isLimit
@[stacks 0318 "positive-stage module limit cone"]
#check @positive_stage_module_completion_limitCone
@[stacks 0318 "positive-stage module limit isomorphism"]
#check @positive_stage_module_system_limit_iso
@[stacks 0318 "positive-stage module inverse projection"]
#check @positive_stage_module_system_limit_iso_inv_π
@[stacks 0318 "positive-stage module forward projection"]
#check @positive_stage_module_system_limit_iso_hom_π
@[stacks 0318 "positive-stage completion family"]
#check @positive_stage_completion_family
@[stacks 0318 "positive-stage completion compatibility"]
#check @positive_stage_completion_family_compat
@[stacks 0318 "positive-stage completion family at positive stages"]
#check @positive_stage_completion_family_pnat
@[stacks 0318 "positive-stage completion cone"]
#check @positive_stage_completion_completion_cone
@[stacks 0318 "positive-stage completion cone naturality"]
#check @positive_stage_completion_completion_cone_naturality
@[stacks 0318 "positive-stage completion hom extensionality"]
#check @positive_stage_completion_completion_hom_ext
@[stacks 0318 "positive-stage completion lift"]
#check @positive_stage_completion_completion_lift
@[stacks 0318 "positive-stage completion lift factorization"]
#check @positive_stage_completion_completion_lift_fac
@[stacks 0318 "positive-stage completion lift uniqueness"]
#check @positive_stage_completion_completion_lift_uniq
@[stacks 0318 "positive-stage completion limit"]
#check @positive_stage_completion_completion_isLimit
@[stacks 0318 "positive-stage completion limit cone"]
#check @positive_stage_completion_completion_limitCone
@[stacks 0318 "positive-stage completion limit isomorphism"]
#check @positive_stage_completion_system_limit_iso
@[stacks 0318 "positive-stage completion inverse projection"]
#check @positive_stage_completion_system_limit_iso_inv_π
@[stacks 0318 "positive-stage completion forward projection"]
#check @positive_stage_completion_system_limit_iso_hom_π

end
