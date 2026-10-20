/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection.Number
import StacksCheckRecall

/-!
# Lemma 72.18.4

The intersection number of invertible modules with a closed subspace proper over
a field is an integer.
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

/- Lemma 72.18.4: in the situation of Definition 72.18.3, the intersection number
`(L 0 ⋯ L (d - 1) · Z)` is an integer. -/
@[stacks 0EDG] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.number_isInteger :
    ∀ {k : Type u} [Field k]
    {X Z : AlgebraicSpace (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper (SchemeRealization.toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)],
    IsLocalization.IsInteger ℤ (number i hZdim L))

end Intersection
end AlgebraicGeometry.AlgebraicSpace.Modules
