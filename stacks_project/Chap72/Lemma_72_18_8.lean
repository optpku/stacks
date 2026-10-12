/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_2
public import stacks_project.Chap71.Definition_71_7_1_AssociatedSheaf
public import stacks_project.Chap72.Definition_72_18_3_Number

/-!
# Lemma 72.18.8

The intersection number of invertible modules with a closed subspace equals the
finite-difference coefficient of the remaining factors on an effective Cartier
divisor cut out by the first restriction.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace Intersection

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- The remaining invertible factors `L 1, …, L (d - 1)` of a nonempty finite family on `X`. -/
def tailFactors {S : Scheme.{u}} {X : AlgebraicSpace S} {d : ℕ} (hd : 0 < d)
    (L : Fin d → X.Modules) : Fin (d - 1) → X.Modules :=
  fun t ↦ L (Fin.cast (Nat.succ_pred_eq_of_pos hd) t.succ)

/-- `tailFactors` evaluates to the corresponding successor factor of the original family. -/
theorem tailFactors_apply {S : Scheme.{u}} {X : AlgebraicSpace S} {d : ℕ} (hd : 0 < d)
    (L : Fin d → X.Modules) (t : Fin (d - 1)) :
    tailFactors hd L t = L (Fin.cast (Nat.succ_pred_eq_of_pos hd) t.succ) := sorry

/-- If every member of a finite family is invertible, then every remaining factor is invertible. -/
instance instIsInvertibleObject_tailFactors
    {S : Scheme.{u}} {X : AlgebraicSpace S} {d : ℕ} (hd : 0 < d)
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)] :
    ∀ t : Fin (d - 1), isInvertibleObject (tailFactors hd L t) := sorry

/-- Lemma 72.18.8: if `k` is a field, `X` is proper over `k`, `Z ⊂ X` is a closed subspace of
dimension `d`, `L 0, …, L (d - 1)` are invertible `𝒪_X`-modules, and `D ⊂ Z` is an effective
Cartier divisor with `(L 0)|_Z ≅ 𝒪_Z(D)`, then
`(L 0 ⋯ L (d - 1) · Z) = (L 1 ⋯ L (d - 1) · D)`. -/
@[stacks 0EDK]
theorem number_eq_tailFactors_of_effectiveCartierDivisor
    {k : Type u} [Field k]
    {X Z D : AlgebraicSpace (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper (toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] [IsLocallyNoetherian D]
    {d : ℕ} (hd : 0 < d) (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Z.Modules] [Abelian D.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    [HasInjectiveResolutions D.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (j : D ⟶ Z) [IsEffectiveCartierDivisor j]
    (hL1 : (pullback i).obj (L ⟨0, hd⟩) ≅ Hom.associatedSheaf j) :
    number i hZdim L = finiteDifferenceNumber (j ≫ i) (tailFactors hd L) := sorry

end Intersection
end AlgebraicGeometry.AlgebraicSpace.Modules
