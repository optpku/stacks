/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Isom
import StacksCheckRecall

/-!
# Isom sheaves of a quotient stack

The Isom sheaf between two atlas images is the relative sheaf of points of the arrow pullback.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidAlgebraicSpace

universe u

/- Lemma 78.22.1. Assume `B → S`, `(U, R, s, t, c)` and `π : 𝒮_U ⟶ [U/R]` are as in
Lemma 78.20.2. Let `S'` be a scheme over `S`. If `x = π(x')` and `y = π(y')` for morphisms
`x', y' : S' ⟶ U`, then `Isom(x, y)` equals `S' ×_{(y', x'), U ×_S U} R` as sheaves over
`S'`. Since `[U/R]` is a stack in groupoids, `Isom(x, y)` is the Hom sheaf of the quotient
stack, and the right-hand side is the sheaf of `S'`-points of `isomPullback G x' y'`. -/
@[stacks 044V] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sheafHom_atlas_isIsomorphic_isomPullback :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {S' : Over S} (x' y' : ofOver S' ⟶ G.U.left),
    IsIsomorphic
      ((Functor.fiberPseudofunctor (fppfQuotientStack G).p).sheafHom
        (Scheme.fppfTopology.over S)
        (((fppfAtlas G).fiberFunctor S').obj (AlgebraicGeometry.AlgebraicSpace.objOfHom x'))
        (((fppfAtlas G).fiberFunctor S').obj (AlgebraicGeometry.AlgebraicSpace.objOfHom y')))
      (isomPullbackSheaf G x' y'))
