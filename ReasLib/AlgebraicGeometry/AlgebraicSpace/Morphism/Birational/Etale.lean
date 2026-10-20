/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PullbackConditions

/-!
# Birational morphisms after affine étale base change

A birational morphism between decent algebraic spaces with finitely many
irreducible components remains birational after affine étale base change,
and its source still has finitely many irreducible components.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The base change of a birational morphism between decent algebraic spaces
with finitely many irreducible components along an affine étale chart has
finitely many irreducible components. -/
instance HasFiniteIrreducibleComponents.pullback_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] {V : Over S} [IsAffine V.left]
    (g : ofOver V ⟶ Y) [Etale g] :
    HasFiniteIrreducibleComponents (pullback f g) :=
  sorry

/-- The second projection of the base change of a birational morphism between
decent algebraic spaces with finitely many irreducible components along an
affine étale chart is birational. -/
instance IsBirational.pullback_snd {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] {V : Over S} [IsAffine V.left]
    (g : ofOver V ⟶ Y) [Etale g] :
    -- Local instance justification (search instability): finite components of `ofOver V` cannot be a global instance, since `g` is not determined by `ofOver V`.
    letI : HasFiniteIrreducibleComponents (ofOver V) :=
      HasFiniteIrreducibleComponents.ofOver_etale g
    IsBirational (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
