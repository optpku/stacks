/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.AsymptoticRiemannRoch
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Proposition 33.45.13 (Asymptotic Riemann-Roch): if `X` is a proper scheme of dimension `d`
over a field `k` and `L` is an ample invertible `𝒪_X`-module, then the dimensions of
`Γ(X, L ^⊗ n)` are eventually given by a degree-`d` polynomial whose leading coefficient is
`Intersection.wholeDegree k f L hXdim / d!` and is positive. -/
@[stacks 0BJ8] #check
  (AlgebraicGeometry.Scheme.Modules.exists_asymptoticRiemannRochPolynomial :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
      [AlgebraicGeometry.Scheme.Modules.IsAmple L]
      {d : ℕ} (hXdim : topologicalKrullDim X = d),
      ∃ P : Polynomial ℚ,
        P.EventuallyEqNat
            (fun n ↦ (Scheme.Hom.cohomologyFinrank f (L ^⊗ (n : ℤ)) 0 : ℚ)) ∧
          P.natDegree = d ∧
          P.leadingCoeff =
            Scheme.Modules.Intersection.wholeDegree k f L hXdim /
              (Nat.factorial d : ℚ) ∧
          0 < P.leadingCoeff)
