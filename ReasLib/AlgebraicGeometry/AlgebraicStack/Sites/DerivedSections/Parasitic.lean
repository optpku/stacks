/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Presheaf.Vanishing
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Inclusion
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Universe
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

/-!
# Derived sections with parasitic cohomology

An unbounded derived object of abelian sheaves on the fppf site of an
algebraic stack has zero derived sections at every flat object if its
cohomology sheaves vanish on flat objects.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/-- The object property of abelian sheaves on the fppf site whose values
vanish at every object with flat 2-Yoneda morphism. -/
def vanishesOnFlat :
    ObjectProperty (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}) :=
  fun F ↦ PresheafWithValues.vanishesOn (isFlat X) F.obj

/-- An unbounded derived object of fppf abelian sheaves whose cohomology
sheaves vanish on flat objects has zero derived sections at every flat object. -/
theorem isZero_rGamma_of_parasitic_cohomology
    (K : DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}))
    (hK : DerivedCategory.cohomologyIn (vanishesOnFlat X) K)
    {x : X.total} (hx : isFlat X x) :
    IsZero ((siteAbelianSectionsDerived (inheritedFppfTopology X) x).obj K) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
