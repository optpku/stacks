/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.FilteredColimit
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.GroupTheory.Torsion

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section Sheaf

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/-- Étale cohomology of a locally torsion abelian sheaf on a quasi-compact and
quasi-separated scheme is an additive torsion group in every natural-number degree. -/
theorem etaleCohomology_isTorsion
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) (n : ℕ) :
    AddMonoid.IsTorsion (F.H' n (globalEtale X)) := sorry

end Sheaf

section Derived

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable
  [Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        (siteAbelianSectionsFunctor X.smallEtaleTopology (globalEtale X)))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]

/-- Étale cohomology of a bounded-below derived object with locally torsion cohomology
sheaves on a quasi-compact and quasi-separated scheme is an additive torsion group in every
integer degree. -/
theorem derivedEtaleCohomology_isTorsion
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn (Sheaf.torsion X.smallEtaleTopology) K)
    (n : ℤ) :
    AddMonoid.IsTorsion
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived X.smallEtaleTopology (globalEtale X)).obj
          (DerivedCategory.Plus.ι.obj K))) := sorry

end Derived

end AlgebraicGeometry.Scheme.Etale

end
