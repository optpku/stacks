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
    (Ideal.Quotient.liftₐ (maximalIdeal R.carrier ^ (nilpotencyIndex A + 1)) α.hom sorry)
    sorry sorry

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
    Along.stronglyCartesianUnop (p := p) fst φ g (g ≫ fst) rfl φ' sorry sorry

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
    (Quiver.Hom.op (toRestrictedHomAppAux ξ f)) inferInstance sorry

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
    (Quiver.Hom.op (τ.1.app m ≫ toRestrictedHomPush η x)) inferInstance sorry

/-- Stage comparison from the original inverse system of `ξ` to the identity-truncation
value of `underline ξ`. -/
private def toRestrictedHomRecoverAppInv {R : CompleteLocalAlgCat Λ k}
    (ξ : Functor.Fiber (Functor.completion p) R) (n : ℕ) :
    ξ.1.system.family n ⟶ toRestrictedHomObj ξ (restrictedIdentity R n) :=
  let m := nilpotencyIndex (R.truncation n)
  have h : m ≤ n := by sorry
  ξ.1.system.transitionMap h ≫ toRestrictedHomPush ξ (restrictedIdentity R n)

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
    (Quiver.Hom.op (𝟙 (ξ.1.system.family n))) sorry sorry

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
