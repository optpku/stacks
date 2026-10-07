module

public import Mathlib.Algebra.MvPolynomial.Basic
public import ReasLib.CategoryTheory.Monoidal.InvertiblePower
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_40_4
public import stacks_project.Chap67.Lemma_67_40_5
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap72.Lemma_72_17_3_EulerCharacteristic

/-!
# Twists on closed subspaces of algebraic spaces

This leaf owns the tensor twists of a family of invertible modules after
pullback to a closed subspace, together with their Euler characteristic over
a proper field base.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Intersection

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- The exponent of the multilinear monomial `∏ j : Fin d, X j`. -/
def multilinearExponent (d : ℕ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ ↦ 1)

/-- The multilinear exponent is the constant function `1`. -/
theorem multilinearExponent_apply (d : ℕ) (j : Fin d) :
    multilinearExponent d j = 1 := sorry

/-- The `{0, 1}`-valued exponent vector associated to a subset of the factors. -/
def subsetExponent {d : ℕ} (s : Finset (Fin d)) : Fin d → ℤ :=
  fun j ↦ if j ∈ s then 1 else 0

/-- `subsetExponent s` evaluates to `1` on `s` and `0` off `s`. -/
theorem subsetExponent_apply {d : ℕ} (s : Finset (Fin d)) (j : Fin d) :
    subsetExponent s j = if j ∈ s then 1 else 0 := sorry

/-- The pullback to a closed subspace of one integral tensor power in a family of invertible
modules on an algebraic space. -/
noncomputable def pullbackTensorPower
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ) (j : Fin d) : Z.Modules :=
  (AlgebraicSpace.Modules.pullback i).obj (InvertiblePower.obj (L j) (n j))

/-- Unfold `pullbackTensorPower` into pullback of an integral tensor power. -/
theorem pullbackTensorPower_def
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ) (j : Fin d) :
    pullbackTensorPower i L n j =
      (AlgebraicSpace.Modules.pullback i).obj (InvertiblePower.obj (L j) (n j)) := sorry

/-- The ordered tensor twist on a closed subspace formed from a family of pulled-back integral
tensor powers. -/
noncomputable def pullbackTensorTwist
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ) : Z.Modules :=
  (List.finRange d).foldr
    (fun j acc ↦ tensorObj (pullbackTensorPower i L n j) acc)
    (SheafOfModules.unit (structureSheaf Z) : Z.Modules)

/-- The closed-subspace tensor twist unfolds to the ordered finite tensor product of its
pulled-back powers. -/
theorem pullbackTensorTwist_def
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ) :
    pullbackTensorTwist i L n =
      (List.finRange d).foldr
        (fun j acc ↦ tensorObj (pullbackTensorPower i L n j) acc)
        (SheafOfModules.unit (structureSheaf Z) : Z.Modules) := sorry

/-- The concrete pullback tensor twist of invertible modules on a closed subspace of a
locally Noetherian algebraic space proper over a field is coherent. -/
instance instIsCoherentPullbackTensorTwist
    {k : Type u} [Field k] {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ) :
    (pullbackTensorTwist i L n).IsCoherent := sorry

/-- The ordered ambient tensor twist beginning with the pushforward of the structure module of a
closed subspace and followed by integral powers of invertible modules. -/
noncomputable def pushforwardStructureTwist
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ) : X.Modules :=
  (List.finRange d).foldl
    (fun acc j ↦ tensorObj acc (InvertiblePower.obj (L j) (n j)))
    ((AlgebraicSpace.Modules.pushforward i).obj
      (SheafOfModules.unit (structureSheaf Z) : Z.Modules))

/-- The ambient pushforward structure twist unfolds to its ordered finite tensor product. -/
theorem pushforwardStructureTwist_def
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ) :
    pushforwardStructureTwist i L n =
      (List.finRange d).foldl
        (fun acc j ↦ tensorObj acc (InvertiblePower.obj (L j) (n j)))
        ((AlgebraicSpace.Modules.pushforward i).obj
          (SheafOfModules.unit (structureSheaf Z) : Z.Modules)) := sorry

/-- The ambient pushforward structure twist of a closed immersion of locally Noetherian
algebraic spaces proper over a field is coherent. -/
instance instIsCoherentPushforwardStructureTwist
    {k : Type u} [Field k] {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ) :
    (pushforwardStructureTwist i L n).IsCoherent := sorry

/-- The Euler characteristic of the pullback tensor twist on a closed subspace of an algebraic
space proper over a field. -/
noncomputable def eulerCharacteristic
    {k : Type u} [Field k] {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ) : ℤ :=
  AlgebraicGeometry.AlgebraicSpace.eulerCharacteristic
    (𝟙 (Spec (CommRingCat.of k))) (i ≫ toBase X) (pullbackTensorTwist i L n)

/-- The closed-subspace twist Euler characteristic is the Euler characteristic of its concrete
pullback tensor twist. -/
theorem eulerCharacteristic_def
    {k : Type u} [Field k] {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ) :
    eulerCharacteristic i L n =
      AlgebraicGeometry.AlgebraicSpace.eulerCharacteristic
        (𝟙 (Spec (CommRingCat.of k))) (i ≫ toBase X) (pullbackTensorTwist i L n) := sorry

/-- The Euler characteristic of the ambient pushforward structure twist equals that of the
corresponding tensor twist restricted to the closed subspace. -/
theorem eulerCharacteristic_pushforwardStructureTwist_eq
    {k : Type u} [Field k] {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    [Abelian X.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (n : Fin d → ℤ) :
    AlgebraicGeometry.AlgebraicSpace.eulerCharacteristic
        (𝟙 (Spec (CommRingCat.of k))) (toBase X) (pushforwardStructureTwist i L n) =
      eulerCharacteristic i L n := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.Intersection
