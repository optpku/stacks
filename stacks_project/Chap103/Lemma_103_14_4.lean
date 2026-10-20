/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap103.Lemma_103_14_4_LowerShriek
import StacksCheckRecall

/-!
On an algebraic stack, module lower shriek along the lisse-étale and
flat-fppf inclusions is left adjoint to restriction, agrees with abelian
lower shriek, and satisfies `g^* g_! = id`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/- Lemma 103.14.4 (1): there is a functor
g_! : Mod(X_lisse,étale, 𝒪) ⟶ Mod(X_étale, 𝒪_X). -/
@[stacks 0789]
#check (lisseEtaleModuleLowerShriek X)

/- Lemma 103.14.4 (2): lisse-étale module lower shriek is left adjoint to g^*. -/
@[stacks 0789]
#check (lisseEtaleModuleLowerShriek.adjunction X)

/- Lemma 103.14.4 (3): lisse-étale module lower shriek agrees with abelian g_!. -/
@[stacks 0789]
#check (lisseEtaleModuleLowerShriek.underlyingComparison_isIso X)

/- Lemma 103.14.4 (4): g^* g_! = id on lisse-étale modules. -/
@[stacks 0789]
#check (lisseEtaleModuleLowerShriek_unit_app_isIso X)

/- Lemma 103.14.4 (5): there is a functor
g_! : Mod(X_flat,fppf, 𝒪) ⟶ Mod(X_fppf, 𝒪_X). -/
@[stacks 0789]
#check (flatFppfModuleLowerShriek X)

/- Lemma 103.14.4 (6): flat-fppf module lower shriek is left adjoint to g^*. -/
@[stacks 0789]
#check (flatFppfModuleLowerShriek.adjunction X)

/- Lemma 103.14.4 (7): flat-fppf module lower shriek agrees with abelian g_!. -/
@[stacks 0789]
#check (flatFppfModuleLowerShriek.underlyingComparison_isIso X)

/- Lemma 103.14.4 (8): g^* g_! = id on flat-fppf modules. -/
@[stacks 0789]
#check (flatFppfModuleLowerShriek_unit_app_isIso X)

end AlgebraicGeometry.AlgebraicStack
