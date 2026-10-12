/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Lifts
import StacksCheckRecall

/-!
# Lift classes along fibre squares

In a category cofibered in groupoids over `ArtinianLocalAlgCat` satisfying (RS), a
fibre square with a surjective leg induces bijections on isomorphism classes of
lifts.
-/

@[expose] public section

open CategoryTheory
open Functor ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
variable {A A1 A2 A1' P Q : ArtinianLocalAlgCat Λ k}
variable {f1 : A1 ⟶ A} {f2 : A2 ⟶ A} {f1' : A1' ⟶ A1}
variable {π1 : P ⟶ A1} {π2 : P ⟶ A2} {σ1 : Q ⟶ A1'} {σ2 : Q ⟶ P}
variable (hP : IsPullback π1 π2 f1 f2) (hQ : IsPullback σ1 σ2 f1' π1)
variable (hsurj : Function.Surjective f1.hom ∨ Function.Surjective f2.hom)
variable (hf1 : Function.Surjective f1.hom) (hf1' : Function.Surjective f1'.hom)
variable (x : p.Fiber A) (a1 : ObjectLift p f1 x)

/- Remark 90.17.4 (1): in a category cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` satisfying (RS), a fibre square with either `A1 ⟶ A` or
`A2 ⟶ A` surjective induces a bijection
`Lift(x, A1) × Lift(x, A2) ≃ Lift(x, A1 ×_A A2)` of isomorphism classes of lifts
of `x` along the two legs with isomorphism classes of lifts of `x` along
`π1 ≫ f1`. This is `liftsPullbackProdEquiv`. -/
@[stacks 06JH]
#check (CategoryTheory.Functor.liftsPullbackProdEquiv :
  IsPullback π1 π2 f1 f2 →
    (Function.Surjective f1.hom ∨ Function.Surjective f2.hom) →
      (x : p.Fiber A) →
        lifts p f1 x × lifts p f2 x ≃ lifts p (π1 ≫ f1) x)

/- Remark 90.17.4 (2): for a fixed lift `a1` of `x` along `A1 ⟶ A`, the same fibre
square induces a bijection `Lift(a1.domain, A1 ×_A A2) ≃ Lift(x, A2)` of
isomorphism classes of lifts of `a1.domain` along `π1` with isomorphism classes
of lifts of `x` along `A2 ⟶ A`. This is `liftsPullbackSliceEquiv`. -/
@[stacks 06JH]
#check (CategoryTheory.Functor.liftsPullbackSliceEquiv :
  IsPullback π1 π2 f1 f2 →
    (Function.Surjective f1.hom ∨ Function.Surjective f2.hom) →
      {x : p.Fiber A} →
        (a1 : ObjectLift p f1 x) →
          lifts p π1 a1.domain ≃ lifts p f2 x)

/- Remark 90.17.4 (3): a composite of fibre squares with both `A1' ⟶ A1` and
`A1 ⟶ A` surjective, together with a lift `a1` of `x` along `A1 ⟶ A`, induces a
bijection `Lift(a1.domain, A1' ×_A A2) ≃ Lift(a1.domain, A1') × Lift(x, A2)`.
This is `liftsPullbackCompEquiv`. -/
@[stacks 06JH]
#check (CategoryTheory.Functor.liftsPullbackCompEquiv :
  IsPullback π1 π2 f1 f2 →
    IsPullback σ1 σ2 f1' π1 →
      Function.Surjective f1.hom →
        Function.Surjective f1'.hom →
          {x : p.Fiber A} →
            (a1 : ObjectLift p f1 x) →
              lifts p (σ1 ≫ f1') a1.domain ≃
                lifts p f1' a1.domain × lifts p f2 x)
