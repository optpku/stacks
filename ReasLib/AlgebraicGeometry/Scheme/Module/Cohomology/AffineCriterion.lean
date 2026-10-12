/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject

/-!
# An affine criterion from vanishing of first cohomology

A quasi-compact scheme is affine when first cohomology vanishes for every
quasi-coherent ideal subobject of its structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact scheme is affine if the first cohomology of every quasi-coherent ideal
subobject of its structure sheaf vanishes. -/
theorem isAffine_of_H1_vanishes_for_quasiCoherent_idealSheaves
    (X : Scheme.{u}) [CompactSpace X.carrier]
    (hH1 : ∀ I : Scheme.IdealSubobject X, I.toModule.IsQuasicoherent →
      IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj I.toModule).H' 1
        (⊤ : X.Opens))) :
    IsAffine X := sorry

/-- A quasi-compact quasi-separated scheme is affine if the first cohomology of every
finite-type quasi-coherent ideal subobject of its structure sheaf vanishes. -/
theorem isAffine_of_H1_vanishes_for_finiteType_quasiCoherent_idealSheaves
    (X : Scheme.{u}) [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (hH1 : ∀ I : Scheme.IdealSubobject X, I.toModule.IsQuasicoherent →
      I.toModule.IsFiniteType →
        IsZero (((SheafOfModules.toSheaf X.ringCatSheaf).obj I.toModule).H' 1
          (⊤ : X.Opens))) :
    IsAffine X := sorry

end AlgebraicGeometry.Scheme
