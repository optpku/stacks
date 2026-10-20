/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.CanonicalElement
public import stacks_project.Chap98.Remark_98_21_9_Canonical_automorphism_Kaehler

/-!
# Canonical infinitesimal deformation along Kähler differentials

Pulling back a fibre object `x` over `Spec(A)` along the section
`a ↦ (a, d_{A/Λ}(a))` of `A[Ω_{A/Λ}]` produces the canonical lift
in `T_x(Ω_{A/Λ}) = Lift(x, A[Ω_{A/Λ}])`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {Λ A : CommRingCat.{u}} (v : Λ ⟶ A)
variable {σΛ : Spec Λ ⟶ S} {σA : Spec A ⟶ S} (hv : Spec.map v ≫ σΛ = σA)
variable (x : X.p.Fiber (Over.mk σA))

#check (AlgebraicGeometry.GroupoidsOver.canonicalDeformation v hv x :
  X.p.Fiber (Over.mk (specTrivSqZero σA (kaehlerObj v))))

#check (AlgebraicGeometry.GroupoidsOver.canonicalLift v hv x :
  liftCat x (trivSqZeroHom A (kaehlerObj v)) (trivSqZeroHom_comp σA (kaehlerObj v)))

variable [HasStrongRimSchlessinger X] (h_open : IsOpenImmersion σΛ)

#check (AlgebraicGeometry.GroupoidsOver.canonicalElement v hv x h_open :
  (tangentFunctor x).obj (kaehlerObj v))

#check (AlgebraicGeometry.GroupoidsOver.evalCanonical v hv x h_open :
  {M : ModuleCat.{u} A} → (kaehlerObj v ⟶ M) → (tangentFunctor x).obj M)

end AlgebraicGeometry.GroupoidsOver
