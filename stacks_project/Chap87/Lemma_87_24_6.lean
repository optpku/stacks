/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType.Locality
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 87.24.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. The following are equivalent:
`LocallyOfFiniteType f`; `existsSurjectiveEtaleSquare f`, that there is a
commutative square of formal algebraic spaces with representable étale vertical arrows,
`U ⟶ X` surjective, and `U ⟶ V` locally of finite type;
`forallEtaleSquare f`, that every commutative square of formal algebraic
spaces with representable étale vertical arrows has locally-of-finite-type top arrow;
`existsCoverOnTarget f`, that some covering `{Y_ j ⟶ Y}` as in
Definition 87.11.1 has, for each `j`, a covering
`{X_ ji ⟶ Y_ j ×_Y X}` as in Definition 87.11.1 with each `X_ ji ⟶ Y_ j`
locally of finite type; and `existsCoverOnSource f`, that some covering
`{X_ i ⟶ X}` as in Definition 87.11.1 factors as `X_ i ⟶ Y_ i ⟶ Y` with
each `Y_ i` an affine formal algebraic space, each `Y_ i ⟶ Y` representable and étale, and
each `X_ i ⟶ Y_ i` locally of finite type. -/
@[stacks 0ANL]
#check (AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType.tfae :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y] (f : X ⟶ Y),
    List.TFAE [AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType f,
      AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType.existsSurjectiveEtaleSquare f,
      AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType.forallEtaleSquare f,
      AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType.existsCoverOnTarget f,
      AlgebraicGeometry.FormalAlgebraicSpace.LocallyOfFiniteType.existsCoverOnSource f])
