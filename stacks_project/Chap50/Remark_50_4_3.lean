module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.CanonicalAction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.DeRham
open AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
universe u

-- Local instance justification (defeq pin): all checks use the canonical total-derived global-sections shift selected by the public construction.
attribute [local instance] CanonicalAction.globalCommShift

section
variable {X S : Scheme.{u}} (p : X ⟶ S)

/- Remark 50.4.3: each relative de Rham class has its canonical shifted action,
with a regular right-DG-module lift, unit characterization and cup compatibility. -/
@[stacks 0FU7]
#check (AlgebraicGeometry.Scheme.DeRham.CanonicalAction.map p :
  (n : ℤ) → cohomology p n → ShiftedHom (derivedComplex p) (derivedComplex p) n)

#check (AlgebraicGeometry.Scheme.DeRham.CanonicalAction.lifts p :
  (n : ℤ) → (ξ : cohomology p n) →
    (ClassAction.forget p).shiftedHomMap (ClassAction.dgObjectIso p) (ClassAction.dgObjectIso p) n
      (ClassAction.dgLift p n ξ) = CanonicalAction.map p n ξ)

#check (AlgebraicGeometry.Scheme.DeRham.CanonicalAction.one p :
  (n : ℤ) → (ξ : cohomology p n) → ClassAction.valueAtOne p n (ClassAction.dgLift p n ξ) = ξ)

#check (AlgebraicGeometry.Scheme.DeRham.CanonicalAction.characterization p :
  (n : ℤ) → (ξ : cohomology p n) → (φ : ShiftedHom (derivedComplex p) (derivedComplex p) n) →
    (φ = CanonicalAction.map p n ξ ↔
      ∃ ψ : ShiftedHom (ClassAction.dgObject p) (ClassAction.dgObject p) n,
        (ClassAction.forget p).shiftedHomMap (ClassAction.dgObjectIso p) (ClassAction.dgObjectIso p) n ψ = φ ∧
          ClassAction.valueAtOne p n ψ = ξ))

#check (AlgebraicGeometry.Scheme.DeRham.CanonicalAction.onCohomology_apply p :
  (n m : ℤ) → (ξ : cohomology p n) → (η : cohomology p m) →
    (CanonicalAction.onCohomology p n m ξ).hom η = CanonicalAction.cup p n m ξ η)

#check (AlgebraicGeometry.Scheme.DeRham.CanonicalAction.cup_eq_rgammaWedgeCup p :
  (n m : ℤ) → (ξ : cohomology p n) → (η : cohomology p m) →
    CanonicalAction.cup p n m ξ η = CanonicalAction.rgammaWedgeCup p n m ξ η)

#check (AlgebraicGeometry.Scheme.DeRham.CanonicalAction.restrict p :
  (U : X.Opens) → (n : ℤ) → (ξ : cohomology p n) →
    CommSq (CanonicalAction.map p n ξ) (CanonicalAction.restriction p U)
      ((shiftFunctor _ n).map (CanonicalAction.restriction p U))
      (CanonicalAction.restrictedMap p U n ξ))

variable {Y T : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ T} {h : S ⟶ T}
variable (sq : CommSq f p q h)

#check (AlgebraicGeometry.Scheme.DeRham.CanonicalAction.pushforwardCupSquare p sq :
  (n : ℤ) → (ξ : cohomology p n) →
    CommSq (CanonicalTensor.cupProduct sq)
      ((CanonicalTensor.tensor q).map (Prod.mkHom (CanonicalAction.pushedMap p sq n ξ) (𝟙 _)))
      (CanonicalAction.pushedMap p sq n ξ) (CanonicalAction.shiftedCup p sq n))
end
