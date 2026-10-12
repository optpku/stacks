/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import stacks_project.Chap104.Lemma_104_4_2
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 104.8.1

On an algebraic stack, an object of `D(X_fppf)` with parasitic cohomology
sheaves has vanishing derived sections at every flat object.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Limits CategoryTheory.ObjectProperty

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/-- An abelian sheaf on `X_fppf` vanishes on every object of `X` whose
2-Yoneda morphism is flat. This is the abelian reading of the vanishing
condition in Definition 103.9.1. -/
def vanishesOnFlat :
    ObjectProperty (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) :=
  fun F ↦ ∀ (x : X.total), isFlat X x →
    IsZero ((siteAbelianSectionsFunctor (inheritedFppfTopology X) x).obj F)

/-- An abelian sheaf on `X_fppf` satisfies `vanishesOnFlat` if and only if its
sections vanish at every flat object of `X`. -/
theorem vanishesOnFlat_iff
    (F : Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) :
    vanishesOnFlat X F ↔
      ∀ (x : X.total), isFlat X x →
        IsZero ((siteAbelianSectionsFunctor (inheritedFppfTopology X) x).obj F) :=
  sorry

/-- An abelian sheaf on `X_fppf` vanishes on flat objects if and only if it
vanishes at every object whose 2-Yoneda morphism `U ⟶ X` is flat. -/
theorem vanishesOnFlat_iff_yoneda
    (F : Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) :
    vanishesOnFlat X F ↔
      ∀ (x : X.total), Groupoids.Hom.Flat (yonedaHom X x) →
        IsZero ((siteAbelianSectionsFunctor (inheritedFppfTopology X) x).obj F) :=
  sorry

namespace vanishesOnFlat

/-- A sheaf that vanishes on flat objects evaluates to zero at a specified
flat object. -/
theorem isZero {F : Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}}
    (hF : vanishesOnFlat X F) {x : X.total} (hx : isFlat X x) :
    IsZero ((siteAbelianSectionsFunctor (inheritedFppfTopology X) x).obj F) :=
  sorry

end vanishesOnFlat

/-- Lemma 104.8.1: on an algebraic stack `X`, if `K` is an object of
`D(X_fppf)` whose cohomology sheaves are parasitic, then `RΓ(x, K) = 0`
for every object `x` of `X` lying over a scheme `U` such that `U ⟶ X` is
flat. -/
@[stacks 0H13]
theorem isZero_rGamma_of_parasitic_cohomology
    (K : DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}))
    (hK : DerivedCategory.cohomologyIn (vanishesOnFlat X) K)
    {x : X.total} (hx : isFlat X x) :
    IsZero ((siteAbelianSectionsDerived (inheritedFppfTopology X) x).obj K) :=
  sorry

/-- The vanishing of `RΓ(x, K)` for an object `x` of the flat-fppf site,
when the cohomology sheaves of `K` vanish on flat objects. -/
theorem isZero_rGamma_of_parasitic_cohomology_mk
    (K : DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}))
    (hK : DerivedCategory.cohomologyIn (vanishesOnFlat X) K)
    (x : flatFppfSite X) :
    IsZero ((siteAbelianSectionsDerived (inheritedFppfTopology X)
        ((flatFppfInclusion X).obj x)).obj K) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
