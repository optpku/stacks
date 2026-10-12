/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.TrdegBound
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

/- Lemma 48.21.5 (1): if the target stalk at `f x` is Cohen–Macaulay and the
residue-field transcendence degree at every generic point specializing to `x` is at most `r`,
then a nontrivial degree-`i` cohomology stalk of `f⁺!𝒪_Y` forces `-(r : ℤ) ≤ i`. -/
@[stacks 0E9V] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.neg_trdegBound_le_of_cohomologyStalk_nontrivial :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [hS : AlgebraicGeometry.IsNoetherian S]
      {X Y : AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S}
      (f : X ⟶ Y)
      (P : AlgebraicGeometry.Scheme.Compactification.Of Y.obj.left (Over.mk f.hom.left))
      (A : AlgebraicGeometry.Scheme.DerivedQCoh.PlusRightAdjoint
        (AlgebraicGeometry.Scheme.Compactification.Of.ambientMorphism P))
      (x : X.obj.left) (r : ℕ)
      (hCM : Module.CohenMacaulay ((Y.obj.left).presheaf.stalk (f.hom.left x))
        ((Y.obj.left).presheaf.stalk (f.hom.left x)))
      (htrdeg : ∀ ξ : X.obj.left, ξ ∈ genericPoints X.obj.left → Specializes ξ x →
        residueFieldTrdegAt f.hom.left ξ ≤ r)
      (i : ℤ),
      Nontrivial
        (AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologyStalk
          (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingObject f P A).obj
          i x) →
      -(r : ℤ) ≤ i)

/- Lemma 48.21.5 (2): under the same Cohen–Macaulay and generic-point
transcendence-degree hypotheses, the degree `-r` cohomology stalk of `f⁺!𝒪_Y` satisfies
Serre's condition `(S₂)` over `𝒪_{X, x}`. -/
@[stacks 0E9V] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.cohomologyStalk_serreConditionSTwo :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [hS : AlgebraicGeometry.IsNoetherian S]
      {X Y : AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S}
      (f : X ⟶ Y)
      (P : AlgebraicGeometry.Scheme.Compactification.Of Y.obj.left (Over.mk f.hom.left))
      (A : AlgebraicGeometry.Scheme.DerivedQCoh.PlusRightAdjoint
        (AlgebraicGeometry.Scheme.Compactification.Of.ambientMorphism P))
      (x : X.obj.left) (r : ℕ)
      (hCM : Module.CohenMacaulay ((Y.obj.left).presheaf.stalk (f.hom.left x))
        ((Y.obj.left).presheaf.stalk (f.hom.left x)))
      (htrdeg : ∀ ξ : X.obj.left, ξ ∈ genericPoints X.obj.left → Specializes ξ x →
        residueFieldTrdegAt f.hom.left ξ ≤ r),
      Module.SerreConditionS ((X.obj.left).presheaf.stalk x)
        (AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologyStalk
          (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.dualizingObject f P A).obj
          (-(r : ℤ)) x) 2)
