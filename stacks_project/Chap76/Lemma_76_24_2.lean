/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.FiberCriterion
import StacksCheckRecall

/-!
# Flatness of a morphism of algebraic spaces from fibrewise flatness over a Noetherian base

In a triangle `X ⟶ Y ⟶ Z` of algebraic spaces, if `X`, `Y`, `Z` are locally
Noetherian, `X` is flat over `Z`, and every fibre of `X` over a point of `|Z|`
is flat over the corresponding fibre of `Y`, then `X ⟶ Y` is flat. If that
morphism is also surjective, then `Y` is flat over `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.24.2: Flatness of the composite and every induced fibre morphism imply
flatness of the first morphism between locally Noetherian algebraic spaces. -/
@[stacks 0APS] #check
  (AlgebraicGeometry.AlgebraicSpace.Flat.of_fiberFlatOver_of_isLocallyNoetherian :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z),
      [IsLocallyNoetherian X] → [IsLocallyNoetherian Y] → [IsLocallyNoetherian Z] →
      [Flat (f ≫ h)] → (∀ z : Points Z, fiberFlatOver f h z) → Flat f)

/- If the first morphism is also surjective, the second morphism is flat. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Flat.base_of_fiberFlatOver_of_surjective_of_isLocallyNoetherian :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z),
      [IsLocallyNoetherian X] → [IsLocallyNoetherian Y] → [IsLocallyNoetherian Z] →
      [Flat (f ≫ h)] → [Surjective f] → (∀ z : Points Z, fiberFlatOver f h z) → Flat h)

end AlgebraicGeometry.AlgebraicSpace
