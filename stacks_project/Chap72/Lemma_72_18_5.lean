/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection.Additivity
import StacksCheckRecall

/-!
# Lemma 72.18.5

The intersection number of invertible modules with a closed subspace proper over
a field is additive in each invertible factor.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace.Modules.Intersection

section

-- Local instance justification (defeq pin): the imported intersection-number API elaborates HasInjectiveResolutions using Abelian-induced Preadditive and HasZeroMorphisms structures; this alignment makes the resolution binders and all three number applications use those same structures.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 72.18.5: in the situation of Definition 72.18.3, the intersection number
`(L 0 ⋯ L (d - 1) · Z)` is additive in each invertible factor. If
`L idx ≅ tensorObj L' L''`, then
`(L 0 ⋯ L idx ⋯ L (d - 1) · Z) =
(L 0 ⋯ L' ⋯ L (d - 1) · Z) + (L 0 ⋯ L'' ⋯ L (d - 1) · Z)`. -/
@[stacks 0EDH] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Intersection.number_eq_add_of_iso_tensorObj :
    ∀ {k : Type u} [Field k]
    {X Z : AlgebraicSpace (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper (SchemeRealization.toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z] {d : ℕ}
    (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)]
    (idx : Fin d) (L' L'' : X.Modules)
    [isInvertibleObject L'] [isInvertibleObject L'']
    (hTensor : L idx ≅ tensorObj L' L''),
    number i hZdim L =
      number i hZdim (Function.update L idx L') +
        number i hZdim (Function.update L idx L''))

end
