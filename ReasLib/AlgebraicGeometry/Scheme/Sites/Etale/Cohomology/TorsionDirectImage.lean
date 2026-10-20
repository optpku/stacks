module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]

/-- Higher direct images along a quasi-compact and quasi-separated scheme morphism preserve
locally torsion abelian sheaves on the small étale site in every natural-number degree. -/
theorem higherDirectImage_isLocallyTorsion
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsLocallyTorsion F) (n : ℕ) :
    IsLocallyTorsion (((etaleAbelianPushforward.{u + 1} f).rightDerived n).obj F) := sorry

/-- Derived direct image along a quasi-compact and quasi-separated scheme morphism preserves
bounded-below derived objects whose small-étale cohomology sheaves are locally torsion. -/
theorem derivedPushforward_cohomology_isLocallyTorsion
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn (Sheaf.torsion X.smallEtaleTopology) K) :
    DerivedCategory.Plus.cohomologyIn (Sheaf.torsion Y.smallEtaleTopology)
      ((etaleAbelianPushforward.{u + 1} f).rightDerivedFunctorPlus.obj K) := sorry

end AlgebraicGeometry.Scheme.Etale
