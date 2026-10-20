/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Pullback
import StacksCheckRecall

/-!
# Fibre products of formal algebraic spaces

The sheaf fibre product of formal algebraic spaces over a sheaf whose
diagonal is representable by algebraic spaces is again a formal algebraic
space.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ChosenBigFppfSite

universe u v

/- Lemma 87.15.2: Let `S` be a scheme. Let `X`, `Y` be formal algebraic spaces
over `S` and let `Z` be a sheaf whose diagonal is representable by algebraic
spaces. Let `X ⟶ Z` and `Y ⟶ Z` be maps of sheaves. Then the sheaf fibre
product `pullback f g` is a formal algebraic space. -/
@[stacks 0AJ2] #check (AlgebraicGeometry.IsFormalAlgebraicSpace.ofPullback :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (h_diag : representableByAlgebraicSpaces (diag Z)),
    IsFormalAlgebraicSpace (pullback f g))

/- The apex of an `IsPullback` square of morphisms of sheaves into a sheaf
whose diagonal is representable by algebraic spaces is a formal algebraic
space when the two sources are. -/
#check (AlgebraicGeometry.IsFormalAlgebraicSpace.of_isPullback :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z P : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    {f : X ⟶ Z} {g : Y ⟶ Z} {fst : P ⟶ X} {snd : P ⟶ Y}
    (sq : IsPullback fst snd f g)
    (h_diag : representableByAlgebraicSpaces (diag Z)),
    IsFormalAlgebraicSpace P)
