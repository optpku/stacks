/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheafSpace.Comparison
import StacksCheckRecall

/-!
# Lemma 66.27.3

An étale sheaf of sets on an algebraic space determines, under a set-theoretic
smallness hypothesis, an algebraic space étale over the original space, recovering
the sheaf as the associated representable sheaf and as extension by zero of the
terminal sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.27.3 (1): the functor `X` associated to `F` is an algebraic space. -/
@[stacks 0GF6] #check (AlgebraicGeometry.AlgebraicSpace.sheafSpace :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (h : IsEtaleSheafSmall F),
    AlgebraicSpace S)

/- Lemma 66.27.3 (2): the map `X ⟶ Y` is an étale morphism of algebraic spaces. -/
@[stacks 0GF6] #check (AlgebraicGeometry.AlgebraicSpace.instEtale_sheafSpaceTo :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (h : IsEtaleSheafSmall F),
    Etale (sheafSpaceTo F h))

/- Lemma 66.27.3 (3): via `Sh(Y_étale) = Sh(Y_spaces,étale)` we have `F ≅ h_X`. -/
@[stacks 0GF6] #check (AlgebraicGeometry.AlgebraicSpace.sheafSpace_yonedaIso :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (h : IsEtaleSheafSmall F),
    (smallEtaleInclusionDirectImage Y).obj F ≅ sheafSpace_yoneda F h)

/- Lemma 66.27.3 (4): `F ≅ f_small,! *`, where `*` is the terminal object of
`Sh(X_étale)` and `f_small,! *` is the sheafification of the Sites formula
`V ↦ Σ_{φ : V ⟶ X over Y} PUnit`. -/
@[stacks 0GF6] #check (AlgebraicGeometry.AlgebraicSpace.sheafSpace_shriekIso :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (h : IsEtaleSheafSmall F),
    F ≅ sheafSpace_shriekTerminal F h)
