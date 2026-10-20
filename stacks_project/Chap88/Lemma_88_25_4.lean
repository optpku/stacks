/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Faithful
import StacksCheckRecall

/-!
# Uniqueness of morphisms after checking the open complement and the completion

A morphism from a locally Noetherian algebraic space is uniquely determined by its
restriction to the open complement of a closed subset and its map on the
completion along that subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/- Lemma 88.25.4: Let `S` be a scheme. Let `X`, `W` be algebraic spaces over
`S` with `X` locally Noetherian. Let `T ⊂ Points X` be closed. Let `a, b : X ⟶ W`
be morphisms of algebraic spaces over `S` such that `a|_{X \ T} = b|_{X \ T}`
and such that `a_/T = b_/T` as morphisms `X_/T ⟶ W`. Then `a = b`.

Here `a|_{X \ T}` is `openComplementι X T ≫ a : openComplementAlong X T ⟶ W`,
and `a_/T` is `ι X T ≫ a : completionAlong X T ⟶ W.functorOfPoints`. -/
@[stacks 0GI1]
#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.eq_of_restrict_eq :
    ∀ {S : Scheme.{u}} {X W : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) {a b : X ⟶ W}
    (h_open : openComplementι X T ≫ a = openComplementι X T ≫ b)
    (h_completion : ι X T ≫ a = ι X T ≫ b),
    a = b)

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.eq_iff_restrict_eq :
    ∀ {S : Scheme.{u}} {X W : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) {a b : X ⟶ W},
    a = b ↔
      openComplementι X T ≫ a = openComplementι X T ≫ b ∧
        ι X T ≫ a = ι X T ≫ b)

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
