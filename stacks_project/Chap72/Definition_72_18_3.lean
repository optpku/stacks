/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap72.Definition_72_18_3_Number
public import stacks_project.Chap72.Definition_72_18_3_Twist
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Definition 72.18.3: for a field `k`, a proper algebraic space `X` over `k`, a
closed immersion `i : Z ⟶ X` of dimension `d`, and invertible `𝒪_X`-modules
`L 0, …, L (d - 1)`, the intersection number `(L 0 ⋯ L (d - 1) · Z)` is the
coefficient of `n 0 ⋯ n (d - 1)` in the numerical polynomial
`n ↦ χ(X, i_* 𝒪_Z ⊗ L 0^{⊗ n 0} ⊗ ⋯ ⊗ L (d - 1)^{⊗ n (d - 1)}) =
χ(Z, L 0^{⊗ n 0} ⊗ ⋯ ⊗ L (d - 1)^{⊗ n (d - 1)} |_ Z)`.
The equal-factor case is written `(L^d · Z)`. -/
@[stacks 0EDF] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.number :
    ∀ {k : Type u} [Field k]
      {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
      (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
      [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
      {d : ℕ} (hZdim : dimension Z = d)
      [Abelian X.Modules] [Abelian Z.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
      [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
      (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)],
      ℚ)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.number_eq_coeff :
    ∀ {k : Type u} [Field k]
      {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
      (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
      [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
      {d : ℕ} (hZdim : dimension Z = d)
      [Abelian X.Modules] [Abelian Z.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
      [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
      (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
      {P : MvPolynomial (Fin d) ℚ}
      (hP : ∀ n : Fin d → ℤ,
        MvPolynomial.eval (fun j : Fin d ↦ (n j : ℚ)) P =
          (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.eulerCharacteristic i L n : ℚ)),
      AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.number i hZdim L =
        P.coeff (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.multilinearExponent d))

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.eulerCharacteristic_pushforwardStructureTwist_eq :
    ∀ {k : Type u} [Field k]
      {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
      (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
      [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
      [Abelian X.Modules] [Abelian Z.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
      [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
      (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
      (n : Fin d → ℤ),
      AlgebraicGeometry.AlgebraicSpace.eulerCharacteristic
          (𝟙 (Spec (CommRingCat.of k))) (toBase X)
          (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.pushforwardStructureTwist i L n) =
        AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.eulerCharacteristic i L n)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.selfNumber :
    ∀ {k : Type u} [Field k]
      {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
      (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
      [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
      {d : ℕ} (hZdim : dimension Z = d)
      [Abelian X.Modules] [Abelian Z.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
      [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
      (L : X.Modules) [isInvertibleObject L],
      ℚ)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.selfNumber_def :
    ∀ {k : Type u} [Field k]
      {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
      (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
      [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
      {d : ℕ} (hZdim : dimension Z = d)
      [Abelian X.Modules] [Abelian Z.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
      [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
      (L : X.Modules) [isInvertibleObject L],
      AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.selfNumber i hZdim L =
        AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.number i hZdim (fun _ ↦ L))
