/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Finite
public import stacks_project.Chap42.Lemma_42_46_10_Rank

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 49.11.1: for a morphism of schemes `f : Y ⟶ X`, the following are
equivalent: `f` is finite and syntomic; it is finite, flat, and a local complete
intersection; it is finite, flat, locally of finite presentation, and has
local-complete-intersection fibres; locally on the target it is the spectrum of a
quotient of a polynomial ring by as many equations as variables; its derived naive
cotangent complex has Tor-amplitude in `[-1, 0]` in addition to finiteness, flatness,
and local finite presentation; or that complex is perfect of rank zero with the same
Tor-amplitude and the same three properties of `f`. -/
@[stacks 0FKY] #check (AlgebraicGeometry.finiteSyntomic_tfae :
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
    let L : RingedSpace.ModuleDerived Y.toRingedSpace :=
      DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)
    List.TFAE [
      IsFinite f ∧ Syntomic f,
      IsFinite f ∧ Flat f ∧
        LocallyOfType RingHom.IsLocalCompleteIntersection f,
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        ∀ x : X, IsLocalCompleteIntersectionOver (X.residueField x)
          (f.fiberToSpecResidueField x),
      IsFinite f ∧
        ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
          ∃ n : ℕ, ∃ g : Fin n → MvPolynomial (Fin n) Γ(X, U),
            ∃ q : MvPolynomial (Fin n) Γ(X, U) →+* Γ(Y, f ⁻¹ᵁ U),
              Function.Surjective q ∧
                q.comp (MvPolynomial.C : Γ(X, U) →+* MvPolynomial (Fin n) Γ(X, U)) =
                  (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom ∧
                RingHom.ker q = Ideal.span (Set.range g),
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        RingedSpace.HasTorAmplitudeIn L (-1) 0,
      IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
        RingedSpace.ModuleDerived.IsPerfect L ∧
          Scheme.ModuleDerived.IsConstantRank L 0 ∧
        RingedSpace.HasTorAmplitudeIn L (-1) 0])
