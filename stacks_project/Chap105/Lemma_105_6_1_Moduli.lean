/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap105.Definition_105_5_1_Moduli
public import stacks_project.Chap105.Lemma_105_6_1_Weierstrass

/-!
# The Weierstrass classifying cover of M11

The names M11 and weierstrassCover are the source-facing bridges to the existing moduli stack
of elliptic curves and to the classifying 1-morphism of the universal Weierstrass family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The moduli stack M11 of elliptic curves, as a category fibred in groupoids over
Sch / Spec ℤ. -/
abbrev M11 : GroupoidsOver EllipticCurve.Moduli.specInt :=
  EllipticCurve.moduli

/-- M11 is the existing moduli stack of elliptic curves. -/
theorem M11_eq : M11.{u} = EllipticCurve.moduli := sorry

namespace M11

/-- The classifying 1-morphism W to M11 of the universal Weierstrass family
(E_W, f_W, 0_W). -/
def weierstrassCover : GroupoidsOver.slice WeierstrassScheme.overInt ⟶ M11.{u} :=
  WeierstrassScheme.classifying

/-- weierstrassCover is the classifying 1-morphism of (E_W, f_W, 0_W). -/
theorem weierstrassCover_eq :
    weierstrassCover.{u} = WeierstrassScheme.classifying.{u} := sorry

/-- Identity-slice evaluation of the Weierstrass cover recovers the pullback of
(E_W, f_W, 0_W) along id W. -/
theorem weierstrassCover_classifies :
    (FiberedCategoryOver.Groupoids.toFunctor weierstrassCover.{u}).obj
        (Over.mk (𝟙 WeierstrassScheme.overInt)) =
      @EllipticCurve.Moduli.classifyingObj WeierstrassScheme.overInt
        (Over.mk WeierstrassScheme.familyHom) WeierstrassScheme.familyZero
        WeierstrassScheme.instIsEllipticCurve
        (Over.mk (𝟙 WeierstrassScheme.overInt)) := sorry

end M11

end AlgebraicGeometry
