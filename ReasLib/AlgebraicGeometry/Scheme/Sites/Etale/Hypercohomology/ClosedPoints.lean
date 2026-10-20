/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Hypercohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- An unbounded derived object of abelian étale sheaves on a finite-type scheme over a
separably closed field, with cohomology supported in closed points, is zero if and only if
its hypercohomology vanishes in every integer degree. -/
theorem isZero_iff_etaleDerivedHypercohomology_isZero_of_support_closedPoints
    {K : Type u} [Field K] [IsSepClosed K] (X : SchemeOverField K) [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [IsGrothendieckAbelian.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    (Q : DerivedCategory (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}))
    (hsupp : DerivedCategory.cohomologyIn (supportSubsetClosedPoints X.left) Q) :
    IsZero Q ↔ ∀ i : ℤ, IsZero ((hypercohomologyFunctor X.left i).obj Q) := sorry

end AlgebraicGeometry.Scheme.Etale

end
