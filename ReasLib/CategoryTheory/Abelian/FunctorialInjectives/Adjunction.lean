/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Definition
public import ReasLib.CategoryTheory.Adjunction.Abelian

/-!
# Functorial injective embeddings through adjunctions

This leaf transfers a functorial choice of injective embeddings along an adjunction.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

noncomputable section

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {u : A ⥤ B} {v : B ⥤ A}
variable [HasFunctorialInjectives A]

/-- The endofunctor of injective targets transferred through the adjunction. -/
noncomputable abbrev adjointInjectiveFunctor (_adj : v ⊣ u) : B ⥤ B :=
  v ⋙ HasFunctorialInjectives.functor ⋙ u

/-- The injective target in `B` obtained by applying the right adjoint to the chosen
injective target of `v.obj X`. -/
noncomputable abbrev adjointInjectiveObj (_adj : v ⊣ u) (X : B) : B :=
  u.obj (HasFunctorialInjectives.obj (v.obj X))

/-- The transferred injective embedding of `X`. -/
noncomputable abbrev adjointInjectiveApp (adj : v ⊣ u) (X : B) :
    X ⟶ adjointInjectiveObj adj X :=
  adj.homEquiv X _ (HasFunctorialInjectives.ι.app (v.obj X))

/-- The map between transferred injective targets induced by a morphism. -/
noncomputable abbrev adjointInjectiveMap (_adj : v ⊣ u) {X Y : B} (f : X ⟶ Y) :
    adjointInjectiveObj _adj X ⟶ adjointInjectiveObj _adj Y :=
  u.map (HasFunctorialInjectives.map (v.map f))

/-- Naturality of the transferred injective embeddings. -/
theorem adjointInjective_naturality (adj : v ⊣ u) {X Y : B} (f : X ⟶ Y) :
    CommSq f (adjointInjectiveApp adj X) (adjointInjectiveApp adj Y)
      (adjointInjectiveMap adj f) := sorry

/-- Each transferred injective embedding is a monomorphism when the categories are
abelian and the left adjoint is additive, preserves monomorphisms, and detects zero objects. -/
theorem adjointInjective_mono (adj : v ⊣ u)
    [Abelian A] [Abelian B] [v.Additive] [v.PreservesMonomorphisms]
    (h_zero : ∀ X : B, IsZero (v.obj X) → IsZero X) (X : B) :
    Mono (adjointInjectiveApp adj X) := sorry

/-- Each transferred injective target is injective when the left adjoint preserves
monomorphisms. -/
theorem adjointInjective_injective (adj : v ⊣ u) [v.PreservesMonomorphisms] (X : B) :
    Injective (adjointInjectiveObj adj X) := sorry

/-- The natural family of injective embeddings transferred through the adjunction. -/
noncomputable def adjointInjectiveι (adj : v ⊣ u) :
    𝟭 B ⟶ adjointInjectiveFunctor adj where
  app := adjointInjectiveApp adj
  naturality _ _ f := (adjointInjective_naturality adj f).w

namespace HasFunctorialInjectives

/-- A right adjoint transports functorial injective embeddings when its left
adjoint preserves monomorphisms and detects zero objects. -/
@[stacks 0161, reducible, no_expose]
noncomputable def of_rightAdjoint
    (adj : v ⊣ u) [Abelian A] [Abelian B] [v.Additive] [v.PreservesMonomorphisms]
    (h_zero : ∀ X : B, IsZero (v.obj X) → IsZero X) :
    HasFunctorialInjectives B :=
  { functor := adjointInjectiveFunctor adj
    ι := adjointInjectiveι adj
    mono_app := adjointInjective_mono adj h_zero
    injective_obj := adjointInjective_injective adj }

/-- Explicit-source form of `of_rightAdjoint`, useful when the chosen source embeddings carry
universe parameters that should not be reconstructed by typeclass search. -/
@[reducible]
noncomputable def of_rightAdjointWith
    (source : HasFunctorialInjectives A) (adj : v ⊣ u)
    [Abelian A] [Abelian B] [v.Additive] [v.PreservesMonomorphisms]
    (h_zero : ∀ X : B, IsZero (v.obj X) → IsZero X) :
    HasFunctorialInjectives B :=
  @of_rightAdjoint A _ B _ u v source adj _ _ _ _ h_zero

end HasFunctorialInjectives

end

end CategoryTheory
