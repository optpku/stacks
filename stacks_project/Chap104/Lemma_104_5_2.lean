/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap104.Lemma_104_5_2_Comparison
import StacksCheckRecall

/-!
# Lemma 104.5.2

For an algebraic stack `X`, the identity-on-objects comparison
`ε : X_fppf ⟶ X_étale` induces a commutative diagram of unbounded derived
categories of `𝒪_X`-modules, with vertical arrows `ε^*`. The left and middle
vertical arrows are equivalences of triangulated categories, and therefore
induce an equivalence
`D_{LQCoh^{fbc}(𝒪_X)}(X_étale, 𝒪_X) / D_{P_X}(X_étale, 𝒪_X) ⥤ D_QCoh(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/- Lemma 104.5.2 (1): the comparison morphism `ε : X_fppf ⟶ X_étale` induces a
commutative square relating `D_{LQCoh^{fbc}}(𝒪_X)` and `D(𝒪_X)` to the étale
counterparts, with vertical arrows `ε^*`. -/
@[stacks 07B8]
#check (etaleFppfInverseImageDerivedLQCohFbc_comp_inclusion X)

/- Lemma 104.5.2 (2): the comparison morphism `ε : X_fppf ⟶ X_étale` induces a
commutative square relating `D_{Parasitic ∩ LQCoh^{fbc}}(𝒪_X)` and
`D_{LQCoh^{fbc}}(𝒪_X)` to `D_{P_X}(X_étale, 𝒪_X)` and
`D_{LQCoh^{fbc}(𝒪_X)}(X_étale, 𝒪_X)`, with vertical arrows `ε^*`. -/
@[stacks 07B8]
#check (etaleFppfInverseImageDerivedParasitic_comp_inclusion X)

/- Lemma 104.5.2 (3): the middle vertical arrow
`ε^* : D_{LQCoh^{fbc}(𝒪_X)}(X_étale, 𝒪_X) ⥤ D_{LQCoh^{fbc}}(𝒪_X)` is an
equivalence of triangulated categories. -/
@[stacks 07B8]
#check (etaleFppfInverseImageDerivedLQCohFbc.instIsEquivalence X)

/- Lemma 104.5.2 (4): the left vertical arrow
`ε^* : D_{P_X}(X_étale, 𝒪_X) ⥤ D_{Parasitic ∩ LQCoh^{fbc}}(𝒪_X)` is an
equivalence of triangulated categories. -/
@[stacks 07B8]
#check (etaleFppfInverseImageDerivedParasitic.instIsEquivalence X)

/- Lemma 104.5.2 (5): the comparison therefore induces an equivalence
`D_{LQCoh^{fbc}(𝒪_X)}(X_étale, 𝒪_X) / D_{P_X}(X_étale, 𝒪_X) ⥤ D_QCoh(𝒪_X)`. -/
@[stacks 07B8]
#check (etaleFppfInverseImageDerivedQCoh.instIsEquivalence X)

end AlgebraicGeometry.AlgebraicStack
