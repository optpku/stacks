/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.Adjunction
import StacksCheckRecall

/-!
# Lemma 84.6.2

For `K` in `D⁺(X_étale)` on an algebraic space `X` over a scheme `S`, the
canonical maps `π_X⁻¹ K ⟶ Rε_{X,*}(a_X⁻¹ K)` and `K ⟶ Ra_{X,*}(a_X⁻¹ K)` are
isomorphisms, where `a_X = π_X ∘ ε_X` is the morphism of topoi
`Sh((Spaces/X)_fppf) ⟶ Sh(X_étale)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FppfEtale
open CategoryTheory CategoryTheory.GrothendieckTopology

universe u

/- Lemma 84.6.2: both canonical comparison maps are isomorphisms for bounded-below
complexes of abelian small-étale sheaves. -/
@[stacks 0DGG] #check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.piInverseDerivedUnit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})),
    IsIso (piInverseDerivedUnit X K))

#check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.plusAAdjunction_unit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})),
    IsIso ((plusAAdjunction X).unit.app K))

end
