module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap68.Definition_68_22_1_Birational

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

/-- An affine scheme étale over a decent algebraic space with finitely many
irreducible components, viewed via `ofOver`, has finitely many irreducible
components. This cannot be a global instance: the étale morphism `g` is not
determined by `ofOver V`, so Lean rejects a synthesization order. -/
theorem HasFiniteIrreducibleComponents.ofOver_etale {S : Scheme.{u}}
    {Y : AlgebraicSpace S} [IsDecent Y] [HasFiniteIrreducibleComponents Y]
    {V : Over S} [IsAffine V.left] (g : ofOver V ⟶ Y) [Etale g] :
    HasFiniteIrreducibleComponents (ofOver V) :=
  sorry

/-- Lemma 68.22.6 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a birational
morphism of algebraic spaces over `S` which are decent and have finitely many
irreducible components. If `g : ofOver V ⟶ Y` is étale with `V` affine, then
the fibre product `pullback f g` is decent. -/
@[stacks 0B4D]
instance IsDecent.pullback_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] {V : Over S} [IsAffine V.left]
    (g : ofOver V ⟶ Y) [Etale g] [HasPullback f g] : IsDecent (pullback f g) :=
  sorry

/-- Lemma 68.22.6 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a birational
morphism of algebraic spaces over `S` which are decent and have finitely many
irreducible components. If `g : ofOver V ⟶ Y` is étale with `V` affine, then
the fibre product `pullback f g` has finitely many irreducible components. -/
@[stacks 0B4D]
instance HasFiniteIrreducibleComponents.pullback_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] {V : Over S} [IsAffine V.left]
    (g : ofOver V ⟶ Y) [Etale g] [HasPullback f g] :
    HasFiniteIrreducibleComponents (pullback f g) :=
  sorry

/-- Lemma 68.22.6 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a birational
morphism of algebraic spaces over `S` which are decent and have finitely many
irreducible components. If `g : ofOver V ⟶ Y` is étale with `V` affine, then
`pullback.snd f g : pullback f g ⟶ ofOver V` is birational. -/
@[stacks 0B4D]
instance IsBirational.pullback_snd {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    (f : X ⟶ Y) [IsBirational f] {V : Over S} [IsAffine V.left]
    (g : ofOver V ⟶ Y) [Etale g] [HasPullback f g] :
    -- Local instance justification (search instability): finite components of `ofOver V` cannot be a global instance, since `g` is not determined by `ofOver V`.
    letI : HasFiniteIrreducibleComponents (ofOver V) :=
      HasFiniteIrreducibleComponents.ofOver_etale g
    IsBirational (pullback.snd f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
