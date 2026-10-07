module

public import Mathlib.RingTheory.Length
public import Mathlib.Topology.Sober
public import ReasLib.RingTheory.MvPolynomial.Numerical
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Lemma_66_29_4_Stalk
public import stacks_project.Chap67.Definition_67_15_4_SchemeTheoreticSupport
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap72.Definition_72_18_3_Twist
public import stacks_project.Chap72.Lemma_72_4_7_IntegralClosed
public import stacks_project.Chap72.Lemma_72_17_3_EulerCharacteristic
public import stacks_project.Chap72.Lemma_72_18_1_MultiTwist

/-!
# Lemma 72.18.2

The Euler characteristic of integral multi-twists of a coherent module, after
subtracting length-weighted restrictions to the top-dimensional irreducible
components of the support, is a numerical polynomial of total degree strictly
less than the dimension of the support.
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
    [Proper (toBase X)] [IsLocallyNoetherian X]
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
  eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (toBase X) (multiTwist F L n) -
    ∑ a : ι,
      ((Module.length (etaleLocalRing X (xbar a)) (stalkModuleCat (xbar a) F)).toNat : ℤ) *
        Intersection.eulerCharacteristic (iZ a) L n

/-- Unfold `eulerCharacteristicMultiTwistSubTopDimComponentSum` into its defining difference of
Euler characteristics. -/
theorem eulerCharacteristicMultiTwistSubTopDimComponentSum_def
    {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Proper (toBase X)] [IsLocallyNoetherian X]
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
      eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (toBase X) (multiTwist F L n) -
        ∑ a : ι,
          ((Module.length (etaleLocalRing X (xbar a)) (stalkModuleCat (xbar a) F)).toNat : ℤ) *
            Intersection.eulerCharacteristic (iZ a) L n :=
  sorry

/-- Lemma 72.18.2: let `k` be a field, let `X` be a proper algebraic space over `k`, let `F`
be a coherent `𝒪_X`-module, and let `L 1, …, L r` be invertible `𝒪_X`-modules. Let
`d = dim(Supp(F))`, let `Z i ⊂ X` be the irreducible components of `Supp(F)` of dimension
`d`, let `x̄ i` be a geometric generic point of `Z i`, and set
`m i = length_{𝒪_{X, x̄ i}}(F_{x̄ i})`. Then
`n ↦ χ(X, F ⊗ L 1^{⊗ n 1} ⊗ ⋯ ⊗ L r^{⊗ n r}) - ∑ i m i χ(Z i, L 1^{⊗ n 1} ⊗ ⋯ ⊗ L r^{⊗ n r} |_ Z i)`
is a numerical polynomial in `n 1, …, n r` of total degree `< d`. -/
@[stacks 0EDE]
theorem eulerCharacteristic_multiTwist_sub_topDimComponentSum_isMvNumericalPolynomialOfTotalDegreeLT
    {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Proper (toBase X)] [IsLocallyNoetherian X] [IsDecent X]
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
