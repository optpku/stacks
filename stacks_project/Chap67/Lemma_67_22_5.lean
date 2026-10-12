/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_22_5_EtaleLocal

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

open Scheme.Germ.MorphismProperty

/-- Lemma 67.22.5 (1): let `Q` be a property of morphisms of scheme germs which is étale
local on the source-and-target, let `S` be a scheme, let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`, and let `x` be a point of `|X|`. Then `Q` holds for the induced
germ morphism of every étale scheme square through `x` if and only if it holds for some
such square. -/
@[stacks 04NC]
theorem forallEtaleSquareAt_iff_existsEtaleSquareAt {S : Scheme.{u}}
    {Q : MorphismProperty Scheme.Germ.{u}}
    (hQ : IsEtaleLocal Q)
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    forallEtaleSquareAt Q f x ↔ existsEtaleSquareAt Q f x :=
  sorry

/-- Lemma 67.22.5 (2): if `X` and `Y` are representable, then the existence of an étale
scheme square through the image of `u` with property `Q` is equivalent to `Q` on the germ
morphism `(U.left, u) ⟶ (V.left, h.left u)`. -/
@[stacks 04NC]
theorem existsEtaleSquareAt_ofOverMap_iff {S : Scheme.{u}}
    {Q : MorphismProperty Scheme.Germ.{u}}
    (hQ : IsEtaleLocal Q)
    {U V : Over S} (h : U ⟶ V) (u : U.left) :
    existsEtaleSquareAt Q (ofOverMap h) (ofOver.pointsEquiv U u) ↔
      Q (ofOverGermHom h u) :=
  sorry

/-- If `X` and `Y` are representable, then every étale scheme square through the image of
`u` has property `Q` if and only if `Q` holds on the germ morphism
`(U.left, u) ⟶ (V.left, h.left u)`. -/
theorem forallEtaleSquareAt_ofOverMap_iff {S : Scheme.{u}}
    {Q : MorphismProperty Scheme.Germ.{u}}
    (hQ : IsEtaleLocal Q)
    {U V : Over S} (h : U ⟶ V) (u : U.left) :
    forallEtaleSquareAt Q (ofOverMap h) (ofOver.pointsEquiv U u) ↔
      Q (ofOverGermHom h u) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
