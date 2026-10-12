/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ProEtale.Comparison
import StacksCheckRecall

/-!
# Lemma 61.17.4

The unbounded derived adjunction unit of the small-to-big pro-étale comparison
is an isomorphism on `D(S.ProEt)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory

noncomputable section

universe u

/- Lemma 61.17.4: for a scheme `S` and `K` in `D(S.ProEt)`, the canonical map
`K ⟶ Rπ_{S,*}(π_S⁻¹ K)` is an isomorphism. -/
@[stacks 0F6A] #check
  (AlgebraicGeometry.Scheme.ProEt.piDerivedAdjunction_unit_isIso :
    ∀ (S : Scheme.{u}) (K : DerivedCategory (Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1})),
      IsIso ((ProEt.piDerivedAdjunction S).unit.app K))
