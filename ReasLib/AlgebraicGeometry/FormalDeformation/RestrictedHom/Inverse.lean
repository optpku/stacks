/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.FormalDeformation.RestrictedHom
public import ReasLib.AlgebraicGeometry.FormalDeformation.Along
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Nilpotency
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Coimage
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Truncation

/-!
# Nilpotency factorization and the explicit inverse `underline ξ`

An object `α : R ⟶ inclusion.obj A` of `underline R |_{C_Λ}` factors uniquely through
the identity truncation of `R` at the nilpotency index of `A`. Pushing the corresponding
stage of a formal object along that factor yields the cofibered quasi-inverse of
`fromRestrictedHom`. Truncation index `n` denotes the quotient by the power `n + 1`;
thus `nilpotencyIndex A + 1` is the least vanishing positive exponent.
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite ArtinianLocalAlgCat CompleteLocalAlgCat
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject

noncomputable section

set_option backward.privateInPublic true

/-- Unique factorization of `α : R ⟶ inclusion.obj A` through the identity truncation
`R.truncation (nilpotencyIndex A)`. -/
def truncationFactor {R : CompleteLocalAlgCat Λ k} {A : ArtinianLocalAlgCat Λ k}
    (α : R ⟶ inclusion.obj A) :
    R.truncation (nilpotencyIndex A) ⟶ A :=
  ArtinianLocalAlgCat.Hom.of
    (Ideal.Quotient.liftₐ (maximalIdeal R.carrier ^ (nilpotencyIndex A + 1)) α.hom (by
      intro r hr
      letI : IsLocalHom α.hom := α.isLocalHom
      letI : IsLocalHom α.hom.toRingHom := isLocalHom_toRingHom α.hom
      have hlocal : maximalIdeal R.carrier ≤
          (maximalIdeal A.carrier).comap α.hom.toRingHom :=
        le_of_eq (IsLocalRing.maximalIdeal_comap α.hom.toRingHom).symm
      have hpow := (pow_le_pow_left' hlocal (nilpotencyIndex A + 1)).trans
        (Ideal.le_comap_pow (f := α.hom.toRingHom)
          (K := maximalIdeal A.carrier) (nilpotencyIndex A + 1))
      have hzero : maximalIdeal A.carrier ^ (nilpotencyIndex A + 1) = ⊥ :=
        nilpotencyIndex_pow_eq_bot A
      rw [hzero] at hpow
      exact (Ideal.mem_bot.mp (hpow hr))))
    sorry sorry

/-- The identity truncation followed by the included factor recovers `α`. -/
theorem truncationFactor_spec {R : CompleteLocalAlgCat Λ k} {A : ArtinianLocalAlgCat Λ k}
    (α : R ⟶ inclusion.obj A) :
    truncationToInclusion R (nilpotencyIndex A) ≫ inclusion.map (truncationFactor α) = α :=
  by
    have ext {R S : CompleteLocalAlgCat Λ k} {f g : R ⟶ S}
        (h : f.hom = g.hom) : f = g := by
      rcases f with ⟨f, hf, hfc⟩
      rcases g with ⟨g, hg, hgc⟩
      change f = g at h
      subst g
      rfl
    apply ext
    apply AlgHom.ext
    intro r
    rfl

/-- A morphism through the identity truncation that recovers `α` equals `truncationFactor α`. -/
theorem truncationFactor_unique {R : CompleteLocalAlgCat Λ k} {A : ArtinianLocalAlgCat Λ k}
    (α : R ⟶ inclusion.obj A) (β : R.truncation (nilpotencyIndex A) ⟶ A)
    (hβ : truncationToInclusion R (nilpotencyIndex A) ≫ inclusion.map β = α) :
    β = truncationFactor α := by
  apply ArtinianLocalAlgCat.hom_ext
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro r
  exact congrArg (fun f : R ⟶ inclusion.obj A ↦ f.hom r) hβ

/-- The stored quotient square determines a comparison after factoring an Artinian test map. -/
theorem truncationFactor_baseTrunc {p : F ⥤ ArtinianLocalAlgCat Λ k}
    {ξ η : FormalObject p} (a : ξ ⟶ η)
    {A : ArtinianLocalAlgCat Λ k} (α : η.base ⟶ inclusion.obj A) :
    a.baseTrunc (nilpotencyIndex A) ≫ truncationFactor α =
      truncationFactor (a.base ≫ α) := by
  apply ArtinianLocalAlgCat.hom_ext
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro r
  have h := DFunLike.congr_fun (a.baseTrunc_spec (nilpotencyIndex A)) r
  exact congrArg (truncationFactor α).hom h

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}
variable [hp : Functor.IsFibered.InGroupoids p.op]

/-- Stage `n` of a completion fibre over `R` lies over `R.truncation n`. -/
theorem stageOverFiber {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R) (n : ℕ) :
    p.obj (ξ.1.system.family n) = R.truncation n :=
  (ξ.1.over_obj n).trans (congrArg (fun b : CompleteLocalAlgCat Λ k ↦ b.truncation n) ξ.2)

/-- Value of `underline ξ` on an object `⟨A, α⟩` of `underline R |_{C_Λ}`: the pushforward
`α_{m,*} ξ_m` along the nilpotency factor of `α`. -/
def toRestrictedHomObj {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R)
    (x : (restrictedCoyoneda R).Elements) : F :=
  Along.pushforwardObj (stageOverFiber ξ (nilpotencyIndex x.1)) (truncationFactor x.2)

/-- Cofibered pushforward from the nilpotency stage of `ξ` to `toRestrictedHomObj ξ x`. -/
def toRestrictedHomPush {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R)
    (x : (restrictedCoyoneda R).Elements) :
    ξ.1.system.family (nilpotencyIndex x.1) ⟶ toRestrictedHomObj ξ x :=
  Along.pushforwardMap (stageOverFiber ξ (nilpotencyIndex x.1)) (truncationFactor x.2)

/-- The chosen pushforward arrow lies over the factor of the Artinian test map. -/
theorem toRestrictedHomPush_isHomLift {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R)
    (x : (restrictedCoyoneda R).Elements) :
    p.IsHomLift (truncationFactor x.2) (toRestrictedHomPush ξ x) := by
  have unop_lift {S T : (ArtinianLocalAlgCat Λ k)ᵒᵖ} {a b : Fᵒᵖ}
      (f : S ⟶ T) (φ : a ⟶ b) (h : p.op.IsHomLift f φ) :
      p.IsHomLift f.unop φ.unop := by
    cases h
    exact IsHomLift.map (p := p) _
  exact unop_lift _ _
    (inferInstance : p.op.IsHomLift (truncationFactor x.2).op
      (Functor.IsPreFibered.pullbackMap (p := p.op)
        (congrArg Opposite.op (stageOverFiber ξ (nilpotencyIndex x.1)))
        (truncationFactor x.2).op))

omit hp in
private theorem stronglyCartesianUnop_isHomLift
    {U V W : (ArtinianLocalAlgCat Λ k)ᵒᵖ} {x y z : Fᵒᵖ}
    (f : U ⟶ V) (φ : y ⟶ x) (g : W ⟶ U) (f' : W ⟶ V)
    (hf' : f' = g ≫ f) (φ' : z ⟶ x)
    (hφ : p.op.IsStronglyCartesian f φ) (hφ' : p.op.IsHomLift f' φ') :
    p.IsHomLift g.unop (Along.stronglyCartesianUnop f φ g f' hf' φ' hφ hφ') := by
  letI := hφ
  letI := hφ'
  have unop_lift {U V : (ArtinianLocalAlgCat Λ k)ᵒᵖ} {a b : Fᵒᵖ}
      (f : U ⟶ V) (φ : a ⟶ b) (h : p.op.IsHomLift f φ) :
      p.IsHomLift f.unop φ.unop := by
    cases h
    exact IsHomLift.map (p := p) _
  exact unop_lift g _
    (inferInstance : p.op.IsHomLift g (Functor.IsStronglyCartesian.map p.op f φ hf' φ'))

omit hp in
/-- Every transition of a formal object induces the corresponding quotient projection. -/
theorem stageTransition_quotient (ξ : FormalObject p) {i j : ℕ} (hij : i ≤ j) :
    (ArtinianLocalAlgCat.Hom.toRingHom
      (eqToHom (ξ.over_obj j).symm ≫ p.map (ξ.system.transitionMap hij) ≫
        eqToHom (ξ.over_obj i))).comp
      (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (j + 1))) =
      Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (i + 1)) := by
  induction hij with
  | refl =>
      have h : ξ.system.transitionMap (Nat.le_refl i) = 𝟙 (ξ.system.family i) :=
        ξ.system.map_id (op i)
      rw [h, p.map_id]
      simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
      rfl
  | @step j hij ih =>
      have hstep : ξ.system.transitionMap (Nat.le_succ_of_le hij) =
          ξ.system.stepMap j ≫ ξ.system.transitionMap hij :=
        ξ.system.map_comp (homOfLE (Nat.le_succ j)).op (homOfLE hij).op
      letI := ξ.over_step j
      have hb : eqToHom (ξ.over_obj (j + 1)).symm ≫ p.map (ξ.system.stepMap j) ≫
          eqToHom (ξ.over_obj j) = ξ.base.truncationMap j :=
        (IsHomLift.fac p (ξ.base.truncationMap j) (ξ.system.stepMap j)).symm
      rw [hstep, p.map_comp]
      have hcomp :
          eqToHom (ξ.over_obj (j + 1)).symm ≫
              (p.map (ξ.system.stepMap j) ≫ p.map (ξ.system.transitionMap hij)) ≫
              eqToHom (ξ.over_obj i) =
            (ξ.base.truncationMap j) ≫
              (eqToHom (ξ.over_obj j).symm ≫ p.map (ξ.system.transitionMap hij) ≫
                eqToHom (ξ.over_obj i)) := by
        rw [← hb]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [hcomp]
      apply RingHom.ext
      intro r
      have h := DFunLike.congr_fun ih r
      exact h

/-- A quotient-square identity determines the morphism after a stage transition. -/
private theorem stageTransition_test {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R) {i j : ℕ} (hij : i ≤ j)
    {A : ArtinianLocalAlgCat Λ k} (f : R.truncation i ⟶ A) (g : R.truncation j ⟶ A)
    (hfg : ∀ r : R.carrier,
      f.hom (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal R ^ (i + 1)) r) =
        g.hom (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal R ^ (j + 1)) r)) :
    (eqToHom (stageOverFiber ξ j).symm ≫ p.map (ξ.1.system.transitionMap hij) ≫
      eqToHom (stageOverFiber ξ i)) ≫ f = g := by
  rcases ξ with ⟨⟨S, xs, hxs, hsteps⟩, hS⟩
  change S = R at hS
  subst S
  apply ArtinianLocalAlgCat.hom_ext
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro r
  have h := DFunLike.congr_fun
    (stageTransition_quotient (p := p) ⟨R, xs, hxs, hsteps⟩ hij) r
  change f.hom
      ((eqToHom (hxs j).symm ≫ p.map (xs.transitionMap hij) ≫ eqToHom (hxs i)).hom
        (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal R ^ (j + 1)) r)) =
    g.hom (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal R ^ (j + 1)) r)
  exact (congrArg f.hom h).trans (hfg r)


/-- A morphism in a completion fibre is vertical at every Artinian stage. -/
theorem fiber_stage_isHomLift {R : CompleteLocalAlgCat Λ k}
    {ξ η : Functor.Fiber (Functor.completion p) R} (τ : ξ ⟶ η) (n : ℕ) :
    p.IsHomLift (𝟙 (R.truncation n)) (τ.1.app n) := by
  rcases ξ with ⟨⟨S, xs, hxs, hsteps⟩, hS⟩
  rcases η with ⟨⟨T, ys, hys, hysteps⟩, hT⟩
  change S = R at hS
  change T = R at hT
  subst S
  subst T
  letI : (Functor.completion p).IsHomLift (𝟙 R) τ.1 := τ.2
  have hb : τ.1.base = 𝟙 R := by
    have h := IsHomLift.fac' (Functor.completion p) (𝟙 R) τ.1
    change τ.1.base = eqToHom (rfl : R = R) ≫ 𝟙 R ≫ eqToHom (rfl : R = R) at h
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h
  have ht : τ.1.baseTrunc n = 𝟙 (R.truncation n) := by
    apply ArtinianLocalAlgCat.hom_ext
    apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro r
    have h := DFunLike.congr_fun (τ.1.baseTrunc_spec n) r
    change (τ.1.baseTrunc n).hom
        (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal R ^ (n + 1)) r) =
      Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal R ^ (n + 1)) r
    change (τ.1.baseTrunc n).hom
        (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal R ^ (n + 1)) r) =
      Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal R ^ (n + 1)) (τ.1.base.hom r) at h
    rw [hb] at h
    exact h
  exact ht ▸ τ.1.over n

/-- Induced map from the source nilpotency stage to the value of `underline ξ` at the
codomain object, connecting inverse-system stages when nilpotency indices differ. -/
private def toRestrictedHomAppAux {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R)
    {x y : (restrictedCoyoneda R).Elements} (f : x ⟶ y) :
    ξ.1.system.family (nilpotencyIndex x.1) ⟶ toRestrictedHomObj ξ y :=
  let m := nilpotencyIndex x.1
  let m' := nilpotencyIndex y.1
  if h : m' ≤ m then
    ξ.1.system.transitionMap h ≫ toRestrictedHomPush ξ y
  else
    let steps := ξ.1.system.transitionMap (Nat.le_of_lt (Nat.not_le.mp h))
    let φ := Quiver.Hom.op steps
    let fst := p.op.map φ
    let φ' := Quiver.Hom.op (toRestrictedHomPush ξ y)
    let g := Quiver.Hom.op
      (eqToHom (stageOverFiber ξ m) ≫ truncationFactor x.2 ≫ f.val)
    Along.stronglyCartesianUnop (p := p) fst φ g (g ≫ fst) rfl φ' inferInstance (by
      let bmap := p.map steps ≫
        (eqToHom (stageOverFiber ξ m) ≫ truncationFactor x.2 ≫ f.val)
      have hq : eqToHom (stageOverFiber ξ m').symm ≫ bmap = truncationFactor y.2 := by
        have hfactor := stageTransition_test ξ (Nat.le_of_lt (Nat.not_le.mp h))
          (truncationFactor x.2 ≫ f.val) (truncationFactor y.2) (fun r ↦ by
            have ht := congrArg (fun q : R ⟶ inclusion.obj y.1 ↦ q.hom r) f.property
            exact ht)
        simpa only [bmap, steps, Category.assoc] using hfactor
      have hlift : p.IsHomLift (eqToHom (stageOverFiber ξ m').symm ≫ bmap)
          (toRestrictedHomPush ξ y) :=
        hq.symm ▸ toRestrictedHomPush_isHomLift ξ y
      exact Along.isHomLift_op
        ((IsHomLift.lift_eqToHom_comp_iff p bmap (toRestrictedHomPush ξ y)
          (stageOverFiber ξ m').symm).mp hlift))

private theorem toRestrictedHomAppAux_isHomLift {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R)
    {x y : (restrictedCoyoneda R).Elements} (f : x ⟶ y) :
    p.IsHomLift (truncationFactor x.2 ≫ f.val) (toRestrictedHomAppAux ξ f) := by
  have reindex {S T : ArtinianLocalAlgCat Λ k} (f g : S ⟶ T) (h : f = g)
      {a b : F} (φ : a ⟶ b) (hf : p.IsHomLift f φ) : p.IsHomLift g φ := h ▸ hf
  dsimp only [toRestrictedHomAppAux]
  split_ifs with h
  · let bmap := eqToHom (stageOverFiber ξ (nilpotencyIndex x.1)).symm ≫
        p.map (ξ.1.system.transitionMap h) ≫
        eqToHom (stageOverFiber ξ (nilpotencyIndex y.1))
    letI : p.IsHomLift bmap (ξ.1.system.transitionMap h) :=
      IsHomLift.of_fac p bmap _ (stageOverFiber ξ (nilpotencyIndex x.1))
        (stageOverFiber ξ (nilpotencyIndex y.1)) rfl
    letI := toRestrictedHomPush_isHomLift ξ y
    have hq : bmap ≫ truncationFactor y.2 = truncationFactor x.2 ≫ f.val :=
      stageTransition_test ξ h (truncationFactor y.2) (truncationFactor x.2 ≫ f.val)
        (fun r ↦ (congrArg (fun q : R ⟶ inclusion.obj y.1 ↦ q.hom r) f.property).symm)
    exact hq ▸ (inferInstance : p.IsHomLift (bmap ≫ truncationFactor y.2)
      (ξ.1.system.transitionMap h ≫ toRestrictedHomPush ξ y))
  · apply (IsHomLift.lift_eqToHom_comp_iff p (truncationFactor x.2 ≫ f.val) _
      (stageOverFiber ξ (nilpotencyIndex x.1))).mp
    apply reindex _ _ (Category.assoc (eqToHom (stageOverFiber ξ (nilpotencyIndex x.1)))
      (truncationFactor x.2) f.val)
    apply stronglyCartesianUnop_isHomLift

/-- Action of `underline ξ` on a morphism of `underline R |_{C_Λ}`, via the strongly
cocartesian comparison of chosen pushforwards. -/
private def toRestrictedHomMap {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R)
    {x y : (restrictedCoyoneda R).Elements} (f : x ⟶ y) :
    toRestrictedHomObj ξ x ⟶ toRestrictedHomObj ξ y :=
  let m := nilpotencyIndex x.1
  let fst := Quiver.Hom.op (truncationFactor x.2)
  let φ :=
    Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op (ξ.1.system.family m))
      (ha := congrArg Opposite.op (stageOverFiber ξ m)) fst
  let g := Quiver.Hom.op f.val
  Along.stronglyCartesianUnop (p := p) fst φ g (g ≫ fst) rfl
    (Quiver.Hom.op (toRestrictedHomAppAux ξ f)) inferInstance
    (Along.isHomLift_op (toRestrictedHomAppAux_isHomLift ξ f))

/-- Vertical comparison of `underline ξ` and `underline η` at a common test object, induced
by a fibre morphism over `R`. -/
private def toRestrictedHom₂ {R : CompleteLocalAlgCat Λ k}
    {ξ η : Functor.Fiber (Functor.completion p) R} (τ : ξ ⟶ η)
    (x : (restrictedCoyoneda R).Elements) :
    toRestrictedHomObj ξ x ⟶ toRestrictedHomObj η x :=
  let m := nilpotencyIndex x.1
  let fst := Quiver.Hom.op (truncationFactor x.2)
  let φ :=
    Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op (ξ.1.system.family m))
      (ha := congrArg Opposite.op (stageOverFiber ξ m)) fst
  let g := Quiver.Hom.op (𝟙 x.1)
  Along.stronglyCartesianUnop (p := p) fst φ g (g ≫ fst) rfl
    (Quiver.Hom.op (τ.1.app m ≫ toRestrictedHomPush η x)) inferInstance (by
      letI := fiber_stage_isHomLift τ m
      letI := toRestrictedHomPush_isHomLift η x
      have h : p.IsHomLift (truncationFactor x.2)
          (τ.1.app m ≫ toRestrictedHomPush η x) := inferInstance
      exact (Category.id_comp fst).symm ▸ Along.isHomLift_op h)

/-- The nilpotency stage of a quotient is bounded by its truncation index. -/
private theorem nilpotencyIndex_truncation_le (R : CompleteLocalAlgCat Λ k) (n : ℕ) :
    nilpotencyIndex (R.truncation n) ≤ n := by
  apply Nat.find_min'
  change IsLocalRing.maximalIdeal (R.carrier ⧸ (CompleteLocalAlgCat.maximalIdeal R ^ (n + 1))) ^
    (n + 1) = ⊥
  rw [← IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal R ^ (n + 1)))
    Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
  exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker])


/-- Stage comparison from the original inverse system of `ξ` to the identity-truncation
value of `underline ξ`. -/
private def toRestrictedHomRecoverAppInv {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R) (n : ℕ) :
    ξ.1.system.family n ⟶ toRestrictedHomObj ξ (restrictedIdentity R n) :=
  let m := nilpotencyIndex (R.truncation n)
  have h : m ≤ n := nilpotencyIndex_truncation_le R n
  ξ.1.system.transitionMap h ≫ toRestrictedHomPush ξ (restrictedIdentity R n)

private theorem toRestrictedHomRecoverAppInv_isHomLift {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R) (n : ℕ) :
    p.IsHomLift (𝟙 (R.truncation n)) (toRestrictedHomRecoverAppInv ξ n) := by
  let m := nilpotencyIndex (R.truncation n)
  have h : m ≤ n := nilpotencyIndex_truncation_le R n
  let bmap := eqToHom (stageOverFiber ξ n).symm ≫
    p.map (ξ.1.system.transitionMap h) ≫ eqToHom (stageOverFiber ξ m)
  letI : p.IsHomLift bmap (ξ.1.system.transitionMap h) :=
    IsHomLift.of_fac p bmap _ (stageOverFiber ξ n) (stageOverFiber ξ m) rfl
  letI := toRestrictedHomPush_isHomLift ξ (restrictedIdentity R n)
  have hq : bmap ≫ truncationFactor (restrictedIdentity R n).2 = 𝟙 (R.truncation n) :=
    stageTransition_test ξ h (truncationFactor (restrictedIdentity R n).2)
      (𝟙 (R.truncation n)) (fun _ ↦ rfl)
  have hc := @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _
    bmap (truncationFactor (restrictedIdentity R n).2)
    (ξ.1.system.transitionMap h) (toRestrictedHomPush ξ (restrictedIdentity R n))
    (inferInstance : p.IsHomLift bmap (ξ.1.system.transitionMap h))
    (toRestrictedHomPush_isHomLift ξ (restrictedIdentity R n))
  exact hq ▸ hc

omit hp in
private theorem identity_isHomLift_op_of_vertical {A : ArtinianLocalAlgCat Λ k}
    {x y : F} (φ : x ⟶ y) (hφ : p.IsHomLift (𝟙 A) φ) :
    p.op.IsHomLift (p.op.map φ.op) (𝟙 x).op := by
  letI := hφ
  let hx := IsHomLift.domain_eq p (𝟙 A) φ
  let hy := IsHomLift.codomain_eq p (𝟙 A) φ
  apply IsHomLift.of_fac' p.op _ _ (congrArg Opposite.op (hx.trans hy.symm)) rfl
  change (p.map (𝟙 x)).op =
    eqToHom (congrArg Opposite.op (hx.trans hy.symm)) ≫ (p.map φ).op ≫ eqToHom rfl
  rw [p.map_id, IsHomLift.fac' p (𝟙 A) φ]
  simp only [eqToHom_op, op_id, Category.id_comp, Category.comp_id,
    eqToHom_trans, eqToHom_refl]

/-- The nilpotency-pushforward functor sends a formal object to the based functor
whose value at `α` is the pushforward of its nilpotency stage along the quotient factor. -/
def toRestrictedHom (R : CompleteLocalAlgCat Λ k) :
    Functor.Fiber (Functor.completion p) R ⥤ RestrictedHom p R :=
  { obj ξ :=
      { toFunctor :=
          { obj x := (toRestrictedHomObj ξ x : F)
            map f := toRestrictedHomMap ξ f
            map_id := sorry
            map_comp := sorry }
        w := sorry }
    map τ :=
      { toNatTrans :=
          { app x := toRestrictedHom₂ τ x
            naturality := sorry }
        isHomLift' := sorry }
    map_id := sorry
    map_comp := sorry }

/-- `underline ξ` sends `⟨A, α⟩` to the chosen pushforward of `ξ_m` along
`truncationFactor α`, and that value lies over `A`. -/
theorem toRestrictedHom_obj (R : CompleteLocalAlgCat Λ k)
    (ξ : Functor.Fiber (Functor.completion p) R)
    (x : (restrictedCoyoneda R).Elements) :
    ((toRestrictedHom R).obj ξ).obj x = toRestrictedHomObj ξ x ∧
      p.obj (((toRestrictedHom R).obj ξ).obj x) = x.1 := sorry

/-- Stage comparison from the identity-truncation value of `underline ξ` back to the
original inverse system of `ξ`. -/
private def toRestrictedHomRecoverApp {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R) (n : ℕ) :
    toRestrictedHomObj ξ (restrictedIdentity R n) ⟶ ξ.1.system.family n :=
  let inv := toRestrictedHomRecoverAppInv ξ n
  Along.cartesianUnop (p := p) (p.op.map (Quiver.Hom.op inv)) (Quiver.Hom.op inv)
    (Quiver.Hom.op (𝟙 (ξ.1.system.family n)))
    (Functor.IsFibered.InGroupoids.all_isCartesian (p := p.op) (Quiver.Hom.op inv))
    (identity_isHomLift_op_of_vertical inv (toRestrictedHomRecoverAppInv_isHomLift ξ n))

/-- Evaluating `underline ξ` on identity truncations recovers `ξ` up to isomorphism in
the completion fibre. -/
def fromRestrictedHom_toRestrictedHom (R : CompleteLocalAlgCat Λ k)
    (ξ : Functor.Fiber (Functor.completion p) R) :
    (fromRestrictedHom p R).obj ((toRestrictedHom R).obj ξ) ≅ ξ where
  hom :=
    ⟨FormalObject.Hom.of (eqToHom ξ.2.symm)
       (fun n ↦
         eqToHom ((fromRestrictedHom_family p R ((toRestrictedHom R).obj ξ) n).2) ≫
           toRestrictedHomRecoverApp ξ n)
       (fun n ↦
         eqToHom (congrArg (fun b : CompleteLocalAlgCat Λ k ↦ b.truncation n) ξ.2.symm))
       sorry sorry sorry,
      sorry⟩
  inv :=
    ⟨FormalObject.Hom.of (eqToHom ξ.2)
       (fun n ↦
         toRestrictedHomRecoverAppInv ξ n ≫
           eqToHom ((fromRestrictedHom_family p R ((toRestrictedHom R).obj ξ) n).2).symm)
       (fun n ↦
         eqToHom (congrArg (fun b : CompleteLocalAlgCat Λ k ↦ b.truncation n) ξ.2))
       sorry sorry sorry,
      sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The nilpotency-pushforward construction is an equivalence, as a quasi-inverse of
`fromRestrictedHom`. -/
instance toRestrictedHom_isEquivalence (R : CompleteLocalAlgCat Λ k) :
    (toRestrictedHom (p := p) R).IsEquivalence := sorry

end

end FormalObject
