/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.FundamentalClass
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
open AlgebraicGeometry.RingedSpace.ModuleDerived
open scoped AlgebraicGeometry

universe u

/- Lemma 48.29.2: for an lci morphism factored as an immersion followed by a proper
smooth morphism, there is a fundamental-class map from the locally indexed top exterior
power of relative differentials to the relative dualizing module. On each clopen
degree locus, its stalk at `x` is an isomorphism exactly when `f` is smooth at `x`. -/
@[stacks 0E9Z] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.existsFundamentalClass :
    {S : Scheme.{u}} → [IsNoetherian S] →
      {X Y : FiniteTypeSeparatedOver S} → (f : X ⟶ Y) →
      [LocallyOfType RingHom.IsLocalCompleteIntersection f.hom.left] →
      {P : Scheme.{u}} → (i : X.obj.left ⟶ P) → (g : P ⟶ Y.obj.left) →
      (factorization : i ≫ g = f.hom.left) → [IsImmersion i] → [IsProper g] →
      [Smooth g] → (Q : Compactification.Of Y.obj.left (Over.mk f.hom.left)) →
      (A : DerivedQCoh.PlusRightAdjoint (Compactification.Of.ambientMorphism Q)) →
      (r : LocallyConstant X.obj.left ℕ) →
      (ω : RingedSpace.Modules (LocallyRingedSpace.toRingedSpace
        (Scheme.toLocallyRingedSpace X.obj.left))) →
      (hω : IsLocallyShiftedSingle (dualizingObject f Q A).obj ω r) →
      ∃ φ : ∀ n : ℕ,
          (Λ[n] ((RingedSpace.moduleRestrictionToOpen (LocallyRingedSpace.toRingedSpace
            (Scheme.toLocallyRingedSpace X.obj.left))
            (r.fiberClopen n).toOpens).obj
              Ω[LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f.hom.left)])) ⟶
            (RingedSpace.moduleRestrictionToOpen (LocallyRingedSpace.toRingedSpace
              (Scheme.toLocallyRingedSpace X.obj.left))
              (r.fiberClopen n).toOpens).obj ω,
        ∀ (n : ℕ) (x : (r.fiberClopen n).toOpens),
          IsIso (RingedSpace.moduleStalkHom x (φ n)) ↔
            AlgebraicGeometry.Scheme.Hom.SmoothAt f.hom.left x.1)
