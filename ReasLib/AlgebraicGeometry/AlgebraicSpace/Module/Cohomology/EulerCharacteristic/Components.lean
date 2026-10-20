/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Length
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection.Twist
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.TensorPower.Multi
public import ReasLib.RingTheory.MvPolynomial.Numerical

/-!
# Euler characteristics and top-dimensional support components

The difference between a multi-twist Euler characteristic and the generic-length-weighted
contributions from its top-dimensional support components has lower total degree.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.TensorPower
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- The Euler characteristic of an integral multi-twist of a coherent module, minus the
stalk-length-weighted Euler characteristics of the corresponding restrictions to a finite
family of closed subspaces. -/
noncomputable def eulerCharacteristicMultiTwistSubTopDimComponentSum
    {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Proper (SchemeRealization.toBase X)] [IsLocallyNoetherian X]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsCoherent] {r : ℕ} (L : Fin r → X.Modules)
    [∀ j : Fin r, isInvertibleObject (L j)]
    {ι : Type u} [Fintype ι] {Z : ι → AlgebraicSpace (Spec (CommRingCat.of k))}
    (iZ : (a : ι) → Z a ⟶ X) [∀ a, IsClosedImmersion (iZ a)]
    [∀ a, IsLocallyNoetherian (Z a)] [∀ a, Abelian (Z a).Modules]
    [∀ a, HasInjectiveResolutions (Z a).Modules]
    (xbar : ι → GeometricPoint X) (n : Fin r → ℤ) : ℤ :=
  eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (SchemeRealization.toBase X) (multiTwist F L n) -
    ∑ a : ι,
      ((Module.length (etaleLocalRing X (xbar a)) (stalkModuleCat (xbar a) F)).toNat : ℤ) *
        Intersection.eulerCharacteristic (iZ a) L n

/-- The component deviation equals the ambient multi-twist Euler characteristic minus the
stalk-length-weighted sum of the restricted Euler characteristics. -/
theorem eulerCharacteristicMultiTwistSubTopDimComponentSum_def
    {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Proper (SchemeRealization.toBase X)] [IsLocallyNoetherian X]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsCoherent] {r : ℕ} (L : Fin r → X.Modules)
    [∀ j : Fin r, isInvertibleObject (L j)]
    {ι : Type u} [Fintype ι] {Z : ι → AlgebraicSpace (Spec (CommRingCat.of k))}
    (iZ : (a : ι) → Z a ⟶ X) [∀ a, IsClosedImmersion (iZ a)]
    [∀ a, IsLocallyNoetherian (Z a)] [∀ a, Abelian (Z a).Modules]
    [∀ a, HasInjectiveResolutions (Z a).Modules]
    (xbar : ι → GeometricPoint X) (n : Fin r → ℤ) :
    eulerCharacteristicMultiTwistSubTopDimComponentSum F L iZ xbar n =
      eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (SchemeRealization.toBase X) (multiTwist F L n) -
        ∑ a : ι,
          ((Module.length (etaleLocalRing X (xbar a)) (stalkModuleCat (xbar a) F)).toNat : ℤ) *
            Intersection.eulerCharacteristic (iZ a) L n :=
  rfl

/-- For a coherent module on a proper algebraic space over a field, subtracting the
geometric-generic-stalk-length-weighted Euler characteristics on all top-dimensional support
components from the multi-twist Euler characteristic yields a numerical polynomial of total
degree strictly below the support dimension. -/
theorem EulerCharacteristic.Components.hasLowerDegree
    {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Proper (SchemeRealization.toBase X)] [IsLocallyNoetherian X] [IsDecent X]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsCoherent] {r : ℕ} (L : Fin r → X.Modules)
    [∀ j : Fin r, isInvertibleObject (L j)]
    {ι : Type u} [Fintype ι] {Z : ι → AlgebraicSpace (Spec (CommRingCat.of k))}
    (iZ : (a : ι) → Z a ⟶ X) [∀ a, IsClosedImmersion (iZ a)] [∀ a, IsIntegral (Z a)]
    [∀ a, IsLocallyNoetherian (Z a)] [∀ a, Abelian (Z a).Modules]
    [∀ a, HasInjectiveResolutions (Z a).Modules]
    (xbar : ι → GeometricPoint X)
    (h_generic : ∀ a, IsGenericPoint (xbar a).image (Set.range (Points.map (iZ a))))
    (h_component : ∀ a,
      Maximal (fun s : Set (Points X) ↦ _root_.IsIrreducible s ∧ s ⊆ moduleSupport F)
        (Set.range (Points.map (iZ a))))
    (h_dim : ∀ a, dimension (Z a) = dimension (schemeTheoreticSupport F).X)
    (h_injective : Function.Injective fun a ↦ Set.range (Points.map (iZ a)))
    (h_exhaustive : ∀ T : IrreducibleCloseds (Points X),
      Maximal (fun s : Set (Points X) ↦ _root_.IsIrreducible s ∧ s ⊆ moduleSupport F)
          T.carrier →
        dimension (ClosedSubspace.ofIrreducibleClosed T).X =
            dimension (schemeTheoreticSupport F).X →
          ∃ a, Set.range (Points.map (iZ a)) = T.carrier) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨
          P.totalDegreeWithBotENat < dimension (schemeTheoreticSupport F).X) ∧
        ∀ n : Fin r → ℤ,
          MvPolynomial.eval (fun j : Fin r ↦ (n j : ℚ)) P =
            (eulerCharacteristicMultiTwistSubTopDimComponentSum F L iZ xbar n : ℚ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
