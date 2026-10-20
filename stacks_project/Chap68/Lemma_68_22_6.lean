/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational.Etale
import StacksCheckRecall

/-!
# Étale affine localization of birational morphisms of algebraic spaces

A birational morphism of decent algebraic spaces with finitely many irreducible
components remains birational after base change along an étale morphism from an
affine scheme, and the fibre product inherits decency and finitely many
irreducible components.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- An affine étale chart over a decent algebraic space with
finitely many irreducible components has finitely many irreducible components. -/
#check (AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponents.ofOver_etale :
  ∀ {S : Scheme.{u}}
    {Y : AlgebraicSpace S} [IsDecent Y] [HasFiniteIrreducibleComponents Y]
    {V : Over S} [IsAffine V.left] (g : ofOver V ⟶ Y) [Etale g],
    HasFiniteIrreducibleComponents (ofOver V))

/- Lemma 68.22.6 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a birational
morphism of algebraic spaces over `S` which are decent and have finitely many
irreducible components. If `g : ofOver V ⟶ Y` is étale with `V` affine, then
the fibre product `pullback f g` is decent. The canonical instance below gives
this conclusion with `Z = ofOver V`, whose decency is supplied by
`AlgebraicGeometry.AlgebraicSpace.instIsDecent_ofOver`. -/
@[stacks 0B4D] #check (AlgebraicGeometry.AlgebraicSpace.instIsDecent_pullback :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsDecent X] [IsDecent Z],
    IsDecent (pullback f g))

/- Lemma 68.22.6 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a birational
morphism of algebraic spaces over `S` which are decent and have finitely many
irreducible components. If `g : ofOver V ⟶ Y` is étale with `V` affine, then
the fibre product `pullback f g` has finitely many irreducible components. -/
@[stacks 0B4D] #check (AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponents.pullback_etale :
  ∀ {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] {V : Over S} [IsAffine V.left]
    (g : ofOver V ⟶ Y) [Etale g],
    HasFiniteIrreducibleComponents (pullback f g))

/- Lemma 68.22.6 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a birational
morphism of algebraic spaces over `S` which are decent and have finitely many
irreducible components. If `g : ofOver V ⟶ Y` is étale with `V` affine, then
`pullback.snd f g : pullback f g ⟶ ofOver V` is birational. -/
@[stacks 0B4D] #check (AlgebraicGeometry.AlgebraicSpace.IsBirational.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] {V : Over S} [IsAffine V.left]
    (g : ofOver V ⟶ Y) [Etale g],
    -- Local instance justification (search instability): finite components of `ofOver V` cannot be a global instance, since `g` is not determined by `ofOver V`.
    letI : HasFiniteIrreducibleComponents (ofOver V) :=
      HasFiniteIrreducibleComponents.ofOver_etale g
    IsBirational (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
