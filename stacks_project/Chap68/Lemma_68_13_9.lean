/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidualSpace
import StacksCheckRecall

/-!
# Factorization through residual spaces of locally Noetherian algebraic spaces

A morphism from a reduced algebraic space whose image on points is contained in
`{x}` factors through a residual space at `x` when the target is locally
Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsResidualSpace

/- Lemma 68.13.9: Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of
algebraic spaces over `S`. Let `x ∈ |X|` be a point. Assume `|f|(|Y|)` is
contained in `{x} ⊂ |X|`, `Y` is reduced, and `X` is locally Noetherian.
Then `f` factors through the residual space `Z_x` of `X` at `x`. -/
@[stacks 0H1S] #check
  (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.exists_lift_of_isLocallyNoetherian :
    ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] [IsLocallyNoetherian X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}),
    ∃ g : Y ⟶ Z, g ≫ ι = f)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.existsUnique_lift_of_isLocallyNoetherian :
    ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] [IsLocallyNoetherian X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] (f : Y ⟶ X)
    (h_image : Set.range (Points.map f) ⊆ {x}),
    ∃! g : Y ⟶ Z, g ≫ ι = f)

#check
  (AlgebraicGeometry.AlgebraicSpace.IsResidualSpace.exists_lift_iff_of_isLocallyNoetherian :
    ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced Y] [IsLocallyNoetherian X]
    {x : Points X} (ι : Z ⟶ X) [IsResidualSpace ι x] (f : Y ⟶ X),
    (∃ g : Y ⟶ Z, g ≫ ι = f) ↔ Set.range (Points.map f) ⊆ {x})

end IsResidualSpace

end AlgebraicGeometry.AlgebraicSpace
