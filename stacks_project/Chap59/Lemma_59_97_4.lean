/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_31_3_EtaleSupport
public import stacks_project.Chap59.Theorem_59_51_3_Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.JacobsonSpace
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped GrothendieckTopologyDerivedSections

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The object property of abelian sheaves on `X_étale` whose étale support is contained in
the closed points of `X`. -/
abbrev supportSubsetClosedPoints (X : Scheme.{u}) :
    ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  fun F ↦ abelianSheafSupport F ⊆ closedPoints X

/-- An abelian étale sheaf satisfies `supportSubsetClosedPoints` if and only if every geometric
point with nonzero geometric stalk has closed image. -/
theorem supportSubsetClosedPoints_iff_geometricStalk {X : Scheme.{u}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    supportSubsetClosedPoints X F ↔
      ∀ xbar : Scheme.GeometricPoint X,
        ¬ IsZero (geometricStalk F xbar) → xbar.image ∈ closedPoints X := sorry

/-- A derived object of abelian étale sheaves has cohomology supported in closed points if and
only if a geometric stalk of some cohomology sheaf can be nonzero only at a closed point. -/
theorem cohomologyIn_supportSubsetClosedPoints_iff_geometricStalk {X : Scheme.{u}}
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    (Q : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    DerivedCategory.cohomologyIn (supportSubsetClosedPoints X) Q ↔
      ∀ xbar : Scheme.GeometricPoint X,
        (∃ n : ℤ, ¬ IsZero (geometricStalk
            ((DerivedCategory.homologyFunctor
                (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) n).obj Q) xbar)) →
          xbar.image ∈ closedPoints X := sorry

section

variable (X : Scheme.{u})
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]

/-- Derived étale hypercohomology `H^i(X, Q)` of an object `Q` of `D(X_étale)`, as the
homology of global derived sections `RΓ(X_étale, Q)`. -/
def etaleDerivedHypercohomology
    (Q : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (i : ℤ) :
    AddCommGrpCat.{u} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
    ((siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X)).obj Q)

/-- Unfolding of `etaleDerivedHypercohomology` as homology of
`siteAbelianSectionsDerived` at `globalEtale X`. -/
theorem etaleDerivedHypercohomology_eq
    (Q : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) (i : ℤ) :
    etaleDerivedHypercohomology X Q i =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X)).obj Q) := sorry

end

/-- Lemma 59.97.4: if `K` is a separably closed field, `X` is a scheme of finite type over
`K`, and `Q` is an object of `D(X_étale)` whose cohomology sheaves have
`abelianSheafSupport` contained in `closedPoints X.left` (that is, a geometric stalk
`Q_x̄` is nonzero only at closed points), then `IsZero Q` if and only if
`IsZero (etaleDerivedHypercohomology X.left Q i)` for every `i : ℤ`. -/
@[stacks 0F1G]
theorem isZero_iff_etaleDerivedHypercohomology_isZero_of_support_closedPoints
    {K : Type u} [Field K] [IsSepClosed K] (X : SchemeOverField K) [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
      (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    [Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor X.left.smallEtaleTopology (globalEtale X.left)))
      (HomologicalComplex.quasiIso
        (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
    (Q : DerivedCategory (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}))
    (hsupp : DerivedCategory.cohomologyIn (supportSubsetClosedPoints X.left) Q) :
    IsZero Q ↔ ∀ i : ℤ, IsZero (etaleDerivedHypercohomology X.left Q i) := sorry

end AlgebraicGeometry.Scheme.Etale

end
