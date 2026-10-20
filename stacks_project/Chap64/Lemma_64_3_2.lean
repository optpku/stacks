/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.PullbackIso

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

/- Lemma 64.3.2. Let `X` be a scheme and `g : X ⟶ X` a morphism. Assume that for
every étale `U : X.Etale` there is an isomorphism `U ≅ (smallEtalePullback g).obj U`
in the slice over `X`, functorial in `U`, equivalently a natural isomorphism
`η : 𝟭 X.Etale ≅ smallEtalePullback g`. Then `g` induces the identity on étale
cohomology of any abelian sheaf. -/
@[stacks 03SP] #check (AlgebraicGeometry.Scheme.Hom.etaleHq_ofSmallEtalePullbackIso_eq_id :
  ∀ {X : Scheme.{u}} (g : X ⟶ X)
    (η : 𝟭 X.Etale ≅ smallEtalePullback g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ),
    etaleHq_ofSmallEtalePullbackIso g η F j = 𝟙 _)
