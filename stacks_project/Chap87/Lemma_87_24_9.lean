/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Pullback
import StacksCheckRecall

/-!
# Fibre products with locally of finite type morphisms of formal algebraic spaces

The fibre product of a locally of finite type morphism of formal algebraic
spaces with a locally Noetherian object is again locally Noetherian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/- Lemma 87.24.9: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of formal algebraic spaces over `S`. If `Z` is locally Noetherian
and `f` is locally of finite type, then the fibre product `Z ×_Y X`, realized
as `pullback f g` up to the canonical symmetry of fibre products, is locally
Noetherian. -/
@[stacks 0AQ8]
#check (AlgebraicGeometry.FormalAlgebraicSpace.IsLocallyNoetherian.instPullbackOfLocallyOfFiniteType :
    ∀ {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z] (f : X ⟶ Y)
    (g : Z ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Z],
    IsLocallyNoetherian (pullback f g))

/- A fibre product of a locally of finite type morphism of formal algebraic
spaces with a locally Noetherian object is locally Noetherian, for an
arbitrary `IsPullback` square. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType.isLocallyNoetherian_of_isPullback :
    ∀ {S : Scheme.{u}}
    {X Y Z P : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [IsFormalAlgebraicSpace P] {f : X ⟶ Y} {g : Z ⟶ Y} {pX : P ⟶ X}
    {pZ : P ⟶ Z} (sq : IsPullback pX pZ f g) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Z], IsLocallyNoetherian P)

end AlgebraicGeometry.FormalAlgebraicSpace
