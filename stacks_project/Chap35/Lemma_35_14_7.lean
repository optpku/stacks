/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Syntomic

/- Lemma 35.14.7 (1): syntomicity descends to `q` under precomposition by a
surjective, flat, locally finitely presented morphism `f`. In the source triangle,
`Syntomic p` and `f ≫ q = p` identify this hypothesis with `Syntomic (f ≫ q)`. -/
@[stacks 05B7] #check
  (AlgebraicGeometry.Syntomic.hasOfPrecompFppf :
    MorphismProperty.HasOfPrecompProperty
      (@Syntomic : MorphismProperty Scheme.{u})
      ((@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :
        MorphismProperty Scheme.{u}))

/- Lemma 35.14.7 (2): if `f` is surjective, flat, and locally finitely presented
and `f ≫ q` is syntomic, then `f` is syntomic. In the source triangle,
`Syntomic p` and `f ≫ q = p` identify this hypothesis with `Syntomic (f ≫ q)`. -/
@[stacks 05B7] #check
  (AlgebraicGeometry.Syntomic.left_of_comp_of_fppf :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
      [Surjective f] [Flat f] [LocallyOfFinitePresentation f],
      Syntomic (f ≫ q) → Syntomic f)

end AlgebraicGeometry.Syntomic
