/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.ModuleCech.Ordered

noncomputable section

universe u

/- 36.6.4.1: The bounded extended alternating Čech complex associated to principal opens,
with the module sheaf in degree zero and the ordered Čech terms in positive degrees. -/
@[stacks 0G7J] #check
  (ModuleCech.ofSections :
    {X : Scheme.{u}} → {c : ℕ} → (Fin c → Γ(X, ⊤)) → X.Modules →
      CochainComplex X.Modules ℕ)

#check
  (ModuleCech.ofSections_X_zero :
    {X : Scheme.{u}} → {c : ℕ} → (f : Fin c → Γ(X, ⊤)) → (ℱ : X.Modules) →
      (ModuleCech.ofSections f ℱ).X 0 = ℱ)

#check
  (ModuleCech.ofSections_X_succ :
    {X : Scheme.{u}} → {c : ℕ} → (f : Fin c → Γ(X, ⊤)) → (ℱ : X.Modules) →
      (p : ℕ) → (ModuleCech.ofSections f ℱ).X (p + 1) =
        term (fun i : ULift.{u} (Fin c) ↦ X.basicOpen (f i.down)) ℱ p)

#check
  (ModuleCech.ofSections_isZero_of_lt :
    {X : Scheme.{u}} → {c n : ℕ} → (f : Fin c → Γ(X, ⊤)) → (ℱ : X.Modules) →
      c < n → IsZero ((ModuleCech.ofSections f ℱ).X n))

end
