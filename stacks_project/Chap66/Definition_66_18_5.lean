/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 66.18.5: let `S` be a scheme and let `X` be an algebraic space over `S`.
The site `X_affine,étale` of `X` is the Grothendieck topology `affineEtaleTopology X` on
the category `affineEtaleSite X` of étale morphisms `φ : ofOver U ⟶ X` with `U` an affine
scheme over `S` and `Etale φ` (morphisms `χ : U ⟶ U'` of schemes over `X` satisfy
`χ ≫ φ' = φ`). Standard étale covering families `{U_i ⟶ U}` are finite families of
affine étale maps that are jointly surjective (Topologies, Definition 34.4.5).
Their covering sieves generate `affineEtaleTopology`. The precoverage
`affineEtalePrecoverage` uses an equivalent sieve presentation, so its displayed
families need not themselves be finite. The fixed scheme universe supplies the
ambient big-site convention. -/
@[stacks 0H01] #check (AlgebraicGeometry.AlgebraicSpace.affineEtaleTopology :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    CategoryTheory.GrothendieckTopology (AlgebraicGeometry.AlgebraicSpace.affineEtaleSite X))
