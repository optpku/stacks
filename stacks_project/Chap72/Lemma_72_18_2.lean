module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.EulerCharacteristic.Components
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.TensorPower
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 72.18.2: let `k` be a field, let `X` be a proper algebraic space over `k`, let `F`
be a coherent `𝒪_X`-module, and let `L 1, …, L r` be invertible `𝒪_X`-modules. Let
`d = dim(Supp(F))`, let `Z i ⊂ X` be the irreducible components of `Supp(F)` of dimension
`d`, let `x̄ i` be a geometric generic point of `Z i`, and set
`m i = length_{𝒪_{X, x̄ i}}(F_{x̄ i})`. Then
`n ↦ χ(X, F ⊗ L 1^{⊗ n 1} ⊗ ⋯ ⊗ L r^{⊗ n r}) - ∑ i m i χ(Z i, L 1^{⊗ n 1} ⊗ ⋯ ⊗ L r^{⊗ n r} |_ Z i)`
is a numerical polynomial in `n 1, …, n r` of total degree `< d`. -/
@[stacks 0EDE] #check (AlgebraicGeometry.AlgebraicSpace.EulerCharacteristic.Components.hasLowerDegree :
    ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
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
          ∃ a, Set.range (Points.map (iZ a)) = T.carrier),
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨
          P.totalDegreeWithBotENat < dimension (schemeTheoreticSupport F).X) ∧
        ∀ n : Fin r → ℤ,
          MvPolynomial.eval (fun j : Fin r ↦ (n j : ℚ)) P =
            (eulerCharacteristicMultiTwistSubTopDimComponentSum F L iZ xbar n : ℚ))
