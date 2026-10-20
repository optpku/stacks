/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RestrictedHom.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory FormalObject CompleteLocalAlgCat
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

/- Remark 90.7.12 (1): evaluation on identity truncations is an equivalence from
morphisms of the restricted representable to the completion fibre. Truncation `n`
uses the power `n + 1`, shifting the source's positive-exponent convention. -/
@[stacks 06HC] #check (FormalObject.fromRestrictedHom_isEquivalence :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    (R : CompleteLocalAlgCat Λ k), (FormalObject.fromRestrictedHom p R).IsEquivalence)

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
  (R : CompleteLocalAlgCat Λ k)

#check (FormalObject.fromRestrictedHom p R :
  RestrictedHom p R ⥤ Functor.Fiber (Functor.completion p) R)

#check (FormalObject.fromRestrictedHom_family p R :
  ∀ (φ : RestrictedHom p R) (n : ℕ),
    let ξ := Functor.Fiber.fiberInclusion.obj ((fromRestrictedHom p R).obj φ)
    p.obj (ξ.system.family n) = R.truncation n ∧
      ξ.system.family n = φ.obj (restrictedIdentity R n))

#check (FormalObject.fromRestrictedHom_step p R :
  ∀ (φ : RestrictedHom p R) (n : ℕ),
    let ξ := Functor.Fiber.fiberInclusion.obj ((fromRestrictedHom p R).obj φ)
    ξ.system.stepMap n = φ.map (restrictedIdentityMap R n) ∧
      p.IsHomLift (R.truncationMap n) (ξ.system.stepMap n))

#check (FormalObject.fromRestrictedHomMap p R :
  ∀ {φ ψ : RestrictedHom p R} (transformation : φ ⟶ ψ),
    fromRestrictedHomObject p R φ ⟶ fromRestrictedHomObject p R ψ)

/- Remark 90.7.12 (2): the forward functor is completion followed by cofibered
2-Yoneda evaluation at the identity. -/
@[stacks 06HC] #check (FormalObject.fromRestrictedHom_comp_phi (p := p) R :
  fromRestrictedHom p R ≅ phiRestricted R ⋙ evaluationAtId R)

/- Remark 90.7.12 (3): the explicit inverse pushes the nilpotency stage forward
along the unique quotient factor of each Artinian test map. -/
@[stacks 06HC] #check (FormalObject.toRestrictedHom (p := p) R :
  Functor.Fiber (Functor.completion p) R ⥤ RestrictedHom p R)

#check (FormalObject.toRestrictedHom_obj (p := p) R :
  ∀ (ξ : Functor.Fiber (Functor.completion p) R) (x : (restrictedCoyoneda R).Elements),
    ((toRestrictedHom R).obj ξ).obj x = toRestrictedHomObj ξ x ∧
      p.obj (((toRestrictedHom R).obj ξ).obj x) = x.1)

#check (FormalObject.fromRestrictedHom_toRestrictedHom (p := p) R :
  ∀ ξ : Functor.Fiber (Functor.completion p) R,
    (fromRestrictedHom p R).obj ((toRestrictedHom R).obj ξ) ≅ ξ)

/- Remark 90.7.12 (4): the cofibered Yoneda section sends a formal object to its
chosen pushforwards along all complete-local test maps. -/
@[stacks 06HC] #check (FormalObject.iota (p := p) R :
  Functor.Fiber (Functor.completion p) R ⥤
    (BasedCategory.ofFunctor (CategoryOfElements.π (coyoneda.obj (Opposite.op R))) ⥤ᵇ
      BasedCategory.ofFunctor (Functor.completion p)))

#check (FormalObject.iota_obj_app (p := p) (R := R) :
  ∀ {S : CompleteLocalAlgCat Λ k} (ξ : Functor.Fiber (Functor.completion p) R) (f : R ⟶ S),
    ((iota R).obj ξ).obj ⟨S, f⟩ = (iotaPush ξ f).target)

#check (FormalObject.iota_id (p := p) (R := R) :
  ∀ ξ : Functor.Fiber (Functor.completion p) R,
    ((iota R).obj ξ).obj ⟨R, 𝟙 R⟩ ≅ ξ.1)

/- Remark 90.7.12 (5): restriction of the Yoneda section followed by evaluation
is isomorphic to the explicit nilpotency-pushforward inverse. -/
@[stacks 06HC] #check (FormalObject.homEquivInverse_iota_iso (p := p) (R := R) :
  ∀ ξ : Functor.Fiber (Functor.completion p) R,
    (psiRestricted R).obj ((iota R).obj ξ) ≅ (toRestrictedHom R).obj ξ)

/- Remark 90.7.12 (6): the Yoneda section is isomorphic to completion of the
explicit inverse. -/
@[stacks 06HC] #check (FormalObject.iota_iso_completion (p := p) (R := R) :
  ∀ ξ : Functor.Fiber (Functor.completion p) R,
    (iota R).obj ξ ≅ (phiRestricted R).obj ((toRestrictedHom R).obj ξ))
