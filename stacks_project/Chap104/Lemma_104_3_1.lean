/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap104.Lemma_104_3_1_Abelian
public import stacks_project.Chap104.Lemma_104_3_1_Module
public import ReasLib.CategoryTheory.Adjunction.BaseChange
import StacksCheckRecall

/-!
# Lemma 104.3.1

On an algebraic stack, abelian and module lower shriek along the lisse-étale
and flat-fppf inclusions admit unbounded left derived functors, left adjoint
to exact derived inverse image, with `g⁻¹ Lg_! = id` and `g^* Lg_! = id`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory
open RingedSite.Cocontinuous

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/- Lemma 104.3.1 (1): the functor g_! on abelian sheaves of the lisse-étale
site has an unbounded left derived functor
Lg_! : D(X_lisse,étale) ⥤ D(X_étale) which is left adjoint to g⁻¹ and
satisfies g⁻¹ Lg_! = id. -/
@[stacks 07AS]
#check (lisseEtaleAbelianLowerShriekDerived X)

@[stacks 07AS]
#check (lisseEtaleAbelianLowerShriekDerived.adjunction X)

@[stacks 07AS]
#check (lisseEtaleAbelianLowerShriekDerived_unit_app_isIso X)

/- Lemma 104.3.1 (2): the functor g_! on modules of the lisse-étale site has an
unbounded left derived functor
Lg_! : D(𝒪_{X_lisse,étale}) ⥤ D(X_étale, 𝒪_X) which is left adjoint to g^*
and satisfies g^* Lg_! = id. -/
@[stacks 07AS]
#check (lisseEtaleModuleLowerShriekDerived X)

@[stacks 07AS]
#check (lisseEtaleModuleLowerShriekDerived.adjunction X)

@[stacks 07AS]
#check (lisseEtaleModuleLowerShriekDerived_unit_app_isIso X)

/- Lemma 104.3.1 (3): the functor g_! on abelian sheaves of the flat-fppf site
has an unbounded left derived functor
Lg_! : D(X_flat,fppf) ⥤ D(X_fppf) which is left adjoint to g⁻¹ and
satisfies g⁻¹ Lg_! = id. -/
@[stacks 07AS]
#check (flatFppfAbelianLowerShriekDerived X)

@[stacks 07AS]
#check (flatFppfAbelianLowerShriekDerived.adjunction X)

@[stacks 07AS]
#check (flatFppfAbelianLowerShriekDerived_unit_app_isIso X)

/- Lemma 104.3.1 (4): the functor g_! on modules of the flat-fppf site has an
unbounded left derived functor
Lg_! : D(𝒪_{X_flat,fppf}) ⥤ D(𝒪_X) which is left adjoint to g^* and
satisfies g^* Lg_! = id. -/
@[stacks 07AS]
#check (flatFppfModuleLowerShriekDerived X)

@[stacks 07AS]
#check (flatFppfModuleLowerShriekDerived.adjunction X)

@[stacks 07AS]
#check (flatFppfModuleLowerShriekDerived_unit_app_isIso X)

/- Warning: it is not a priori clear that Lg_! on modules agrees with Lg_! on
abelian sheaves; the only canonical comparison is the derived underlying mate
of Remark 21.37.3, which is not asserted to be an isomorphism. -/
#check @DerivedBaseChange.mapOfRight

end AlgebraicGeometry.AlgebraicStack
