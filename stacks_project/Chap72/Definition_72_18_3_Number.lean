/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap72.Definition_72_18_3_Twist

/-!
# Intersection numbers of invertible modules on algebraic spaces

This leaf owns the finite-difference definition of intersection numbers of
invertible modules with a closed subspace proper over a field.
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

/-- The multilinear finite difference of the twist Euler characteristic of a family of
invertible modules on a closed subspace. -/
noncomputable def finiteDifferenceNumber
    {k : Type u} [Field k] {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)] : ℚ :=
  ((Finset.univ : Finset (Fin d)).powerset).sum fun s ↦
    ((-1 : ℚ) ^ (d - s.card)) *
      (eulerCharacteristic i L (subsetExponent s) : ℚ)

/-- Unfold `finiteDifferenceNumber` into the signed powerset sum of twist Euler
characteristics. -/
theorem finiteDifferenceNumber_eq_sum
    {k : Type u} [Field k] {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)] :
    finiteDifferenceNumber i L =
      ((Finset.univ : Finset (Fin d)).powerset).sum fun s ↦
        ((-1 : ℚ) ^ (d - s.card)) *
          (eulerCharacteristic i L (subsetExponent s) : ℚ) := sorry

/-- The intersection number of a family of invertible modules with a closed subspace, defined
as the multilinear finite difference of its twist Euler characteristic. -/
noncomputable def number
    {k : Type u} [Field k] {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)] : ℚ :=
  finiteDifferenceNumber i L

/-- An exact-dimension intersection number is its underlying multilinear finite difference. -/
theorem number_eq_finiteDifferenceNumber
    {k : Type u} [Field k] {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)] :
    number i hZdim L = finiteDifferenceNumber i L := sorry

/-- For a closed subspace of dimension `d`, the coefficient of the multilinear monomial in any
polynomial representing the twist Euler characteristic equals the corresponding intersection
number. -/
theorem number_eq_coeff
    {k : Type u} [Field k] {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    {P : MvPolynomial (Fin d) ℚ}
    (hP :
      ∀ n : Fin d → ℤ,
        MvPolynomial.eval (fun j : Fin d ↦ (n j : ℚ)) P =
          (eulerCharacteristic i L n : ℚ)) :
    number i hZdim L = P.coeff (multilinearExponent d) := sorry

/-- The self-intersection number of one invertible module with a closed subspace. -/
noncomputable def selfNumber
    {k : Type u} [Field k] {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    (L : X.Modules) [isInvertibleObject L] : ℚ :=
  number i hZdim (fun _ ↦ L)

/-- The self-intersection number is the intersection number of the constant family of factors. -/
theorem selfNumber_def
    {k : Type u} [Field k] {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    (L : X.Modules) [isInvertibleObject L] :
    selfNumber i hZdim L = number i hZdim (fun _ ↦ L) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.Intersection
