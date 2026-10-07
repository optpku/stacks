module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import stacks_project.Chap90.Lemma_90_7_4_Along
public import stacks_project.Chap90.Remark_90_7_7_Nilpotency
public import stacks_project.Chap90.Remark_90_7_10_Functors
public import stacks_project.Chap90.«90_7_12_1_Yoneda»

/-!
# Nilpotency factorization and the explicit inverse `underline ξ`

An object `α : R ⟶ inclusion.obj A` of `underline R |_{C_Λ}` factors uniquely through
the identity truncation of `R` at the nilpotency index of `A`. Pushing the corresponding
stage of a formal object along that factor yields the cofibered quasi-inverse of
`fromRestrictedHom`.
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

/-- Unique factorization of `α : R ⟶ inclusion.obj A` through the identity truncation
`R.truncation (nilpotencyIndex A)`. -/
def truncationFactor {R : CompleteLocalAlgCat Λ k} {A : ArtinianLocalAlgCat Λ k}
    (α : R ⟶ inclusion.obj A) :
    R.truncation (nilpotencyIndex A) ⟶ A where
  hom :=
    Ideal.Quotient.liftₐ (maximalIdeal R.carrier ^ (nilpotencyIndex A + 1)) α.hom sorry
  isLocalHom := sorry
  residue_compat := sorry

/-- The identity truncation followed by the included factor recovers `α`. -/
theorem truncationFactor_spec {R : CompleteLocalAlgCat Λ k} {A : ArtinianLocalAlgCat Λ k}
    (α : R ⟶ inclusion.obj A) :
    truncationToInclusion R (nilpotencyIndex A) ≫ inclusion.map (truncationFactor α) = α :=
  sorry

/-- A morphism through the identity truncation that recovers `α` equals `truncationFactor α`. -/
theorem truncationFactor_unique {R : CompleteLocalAlgCat Λ k} {A : ArtinianLocalAlgCat Λ k}
    (α : R ⟶ inclusion.obj A) (β : R.truncation (nilpotencyIndex A) ⟶ A)
    (hβ : truncationToInclusion R (nilpotencyIndex A) ≫ inclusion.map β = α) :
    β = truncationFactor α := sorry

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

/-- Induced map from the source nilpotency stage to the value of `underline ξ` at the
codomain object, connecting inverse-system stages when nilpotency indices differ. -/
def toRestrictedHomAppAux {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R)
    {x y : (restrictedCoyoneda R).Elements} (_f : x ⟶ y) :
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
    Along.cartesianUnop (p := p) fst φ φ' sorry sorry

/-- Action of `underline ξ` on a morphism of `underline R |_{C_Λ}`, via the strongly
cocartesian comparison of chosen pushforwards. -/
def toRestrictedHomMap {R : CompleteLocalAlgCat Λ k}
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
    (Quiver.Hom.op (toRestrictedHomAppAux ξ f)) inferInstance sorry

/-- Vertical comparison of `underline ξ` and `underline η` at a common test object, induced
by a fibre morphism over `R`. -/
def toRestrictedHom₂ {R : CompleteLocalAlgCat Λ k}
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
    (Quiver.Hom.op (τ.1.app m ≫ toRestrictedHomPush η x)) inferInstance sorry

/-- Stage comparison from the original inverse system of `ξ` to the identity-truncation
value of `underline ξ`. -/
def toRestrictedHomRecoverAppInv {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R) (n : ℕ) :
    ξ.1.system.family n ⟶ toRestrictedHomObj ξ (restrictedIdentity R n) :=
  let m := nilpotencyIndex (R.truncation n)
  if h : m ≤ n then
    ξ.1.system.transitionMap h ≫ toRestrictedHomPush ξ (restrictedIdentity R n)
  else
    let steps := ξ.1.system.transitionMap (Nat.le_of_lt (Nat.not_le.mp h))
    let φ := Quiver.Hom.op steps
    Along.cartesianUnop (p := p) (p.op.map φ) φ
      (Quiver.Hom.op (toRestrictedHomPush ξ (restrictedIdentity R n))) sorry sorry

/-- The explicit quasi-inverse `underline ξ : underline R |_{C_Λ} ⟶ F` of
`fromRestrictedHom`, sending `α` to `α_{m,*} ξ_m`. -/
def toRestrictedHom (R : CompleteLocalAlgCat Λ k) :
    Functor.Fiber (Functor.completion p) R ⥤ RestrictedHom p R :=
  let _hp := hp
  { obj ξ :=
      { toFunctor :=
          { obj x := @toRestrictedHomObj _ _ _ _ _ _ _ _ _ p hp _ ξ x
            map f := @toRestrictedHomMap _ _ _ _ _ _ _ _ _ p hp _ ξ _ _ f
            map_id := sorry
            map_comp := sorry }
        w := sorry }
    map τ :=
      { toNatTrans :=
          { app x := @toRestrictedHom₂ _ _ _ _ _ _ _ _ _ p hp _ _ _ τ x
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

/-- Stage `n` of `fromRestrictedHom.obj φ` is `φ` applied to the `n`th identity truncation. -/
theorem fromRestrictedHom_system_family (R : CompleteLocalAlgCat Λ k)
    (φ : RestrictedHom p R) (n : ℕ) :
    ((fromRestrictedHom p R).obj φ).1.system.family n = φ.obj (restrictedIdentity R n) :=
  rfl

/-- Stage comparison from the identity-truncation value of `underline ξ` back to the
original inverse system of `ξ`. -/
def toRestrictedHomRecoverApp {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R) (n : ℕ) :
    toRestrictedHomObj ξ (restrictedIdentity R n) ⟶ ξ.1.system.family n :=
  let inv := toRestrictedHomRecoverAppInv ξ n
  Along.cartesianUnop (p := p) (p.op.map (Quiver.Hom.op inv)) (Quiver.Hom.op inv)
    (Quiver.Hom.op (𝟙 (ξ.1.system.family n))) sorry sorry

/-- Evaluating `underline ξ` on identity truncations recovers `ξ` up to isomorphism in
the completion fibre. -/
def fromRestrictedHom_toRestrictedHom (R : CompleteLocalAlgCat Λ k)
    (ξ : Functor.Fiber (Functor.completion p) R) :
    (fromRestrictedHom p R).obj ((toRestrictedHom R).obj ξ) ≅ ξ where
  hom :=
    ⟨{ base := eqToHom ξ.2.symm
       app := fun n ↦
         eqToHom (fromRestrictedHom_system_family R ((toRestrictedHom R).obj ξ) n) ≫
           toRestrictedHomRecoverApp ξ n
       baseTrunc := fun n ↦
         eqToHom (congrArg (fun b : CompleteLocalAlgCat Λ k ↦ b.truncation n) ξ.2.symm)
       over := sorry
       baseTrunc_spec := sorry
       naturality := sorry },
      sorry⟩
  inv :=
    ⟨{ base := eqToHom ξ.2
       app := fun n ↦
         toRestrictedHomRecoverAppInv ξ n ≫
           eqToHom (fromRestrictedHom_system_family R ((toRestrictedHom R).obj ξ) n).symm
       baseTrunc := fun n ↦
         eqToHom (congrArg (fun b : CompleteLocalAlgCat Λ k ↦ b.truncation n) ξ.2)
       over := sorry
       baseTrunc_spec := sorry
       naturality := sorry },
      sorry⟩
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The nilpotency-pushforward construction is an equivalence, as a quasi-inverse of
`fromRestrictedHom`. -/
instance toRestrictedHom_isEquivalence (R : CompleteLocalAlgCat Λ k) :
    (@toRestrictedHom _ _ _ _ _ _ _ _ _ p hp R).IsEquivalence := sorry

end

end FormalObject
