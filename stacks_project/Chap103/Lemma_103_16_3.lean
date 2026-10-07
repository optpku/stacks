module

public import stacks_project.Chap103.Lemma_103_16_3_QCoh
public import stacks_project.Chap103.Lemma_103_16_3_Equivalence
import StacksCheckRecall

/-!
On an algebraic stack, inverse image and lower shriek along the lisse-étale
and flat-fppf inclusions restrict to mutually inverse equivalences on
quasi-coherent modules, send `LQCoh^{fbc}` to quasi-coherent modules on the
small site, and identify the reflector `Q` of Lemma 103.10.1 with `g_! g⁻¹`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory

universe u

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]

/- Lemma 103.16.3 (1): with `g` the lisse-étale inclusion of Lemma 103.14.2,
the functors `g⁻¹ := lisseEtaleModuleInverseImage` and
`g_! := lisseEtaleModuleLowerShriek` restrict to mutually inverse equivalences
between `etaleQCoh X` and `lisseEtaleQCoh X`. -/
@[stacks 07B1]
#check (lisseEtaleQCohEquivalence X)

/- Lemma 103.16.3 (2): if `F` lies in `LQCoh^{fbc}(𝒪_X)`, then
`g⁻¹ F` is quasi-coherent on the lisse-étale site. -/
@[stacks 07B1]
#check lisseEtaleModuleInverseImage.obj_isQuasicoherent_of_lqcohFbc

/- Lemma 103.16.3 (3): if `F` lies in `LQCoh^{fbc}(𝒪_X)`, then
`Q(F) = g_! g⁻¹ F` for `Q := LQCohFbc.toQCoh`. -/
@[stacks 07B1]
#check lisseEtaleToQCohIsoLowerShriekInverseImage

/- Lemma 103.16.3 (4): with `g` the flat-fppf inclusion of Lemma 103.14.2,
the functors `g⁻¹ := flatFppfModuleInverseImage` and
`g_! := flatFppfModuleLowerShriek` restrict to mutually inverse equivalences
between `QCoh X` and `flatFppfQCoh X`. -/
@[stacks 07B1]
#check (flatFppfQCohEquivalence X)

/- Lemma 103.16.3 (5): if `F` lies in fppf `LQCoh^{fbc}(𝒪_X)`, then
`g⁻¹ F` is quasi-coherent on the flat-fppf site. -/
@[stacks 07B1]
#check flatFppfModuleInverseImage.obj_isQuasicoherent_of_lqcohFbc

/- Lemma 103.16.3 (6): if `F` lies in fppf `LQCoh^{fbc}(𝒪_X)`, then
`Q(F) = g_! g⁻¹ F` for `Q := LQCohFbc.toQCoh`. -/
@[stacks 07B1]
#check flatFppfToQCohIsoLowerShriekInverseImage
