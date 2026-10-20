/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection.EffectiveCartier
import StacksCheckRecall

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

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Intersection

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 72.18.8: if `k` is a field, `X` is proper over `k`, `Z ⊂ X` is a closed subspace of
dimension `d`, `L 0, …, L (d - 1)` are invertible `𝒪_X`-modules, and `D ⊂ Z` is an effective
Cartier divisor with `(L 0)|_Z ≅ 𝒪_Z(D)`, then
`(L 0 ⋯ L (d - 1) · Z) = (L 1 ⋯ L (d - 1) · D)`. -/
@[stacks 0EDK] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.number_eq_tail_of_effectiveCartierDivisor :
    ∀ {k : Type u} [Field k]
    {X Z D : AlgebraicSpace (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper (SchemeRealization.toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] [IsLocallyNoetherian D]
    {n : ℕ} (hZdim : dimension Z = n + 1)
    [Abelian X.Modules] [Abelian Z.Modules] [Abelian D.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    [HasInjectiveResolutions D.Modules]
    (L : Fin (n + 1) → X.Modules) [∀ t : Fin (n + 1), isInvertibleObject (L t)]
    (j : D ⟶ Z) [IsEffectiveCartierDivisor j]
    (hL1 : (pullback i).obj (L 0) ≅ Hom.associatedSheaf j),
    number i hZdim L = finiteDifferenceNumber (j ≫ i) (fun t : Fin n ↦ L t.succ))

end AlgebraicGeometry.AlgebraicSpace.Modules.Intersection
