/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtSource.AffineDescent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Local
public import ReasLib.RingTheory.RingHom.FiniteType.FaithfullyFlat

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- Local finite-type quasi-finiteness of scheme morphisms is local on the source for the
étale precoverage. -/
theorem locallyQuasiFiniteIsLocalAtSourceEtale :
    CategoryTheory.MorphismProperty.IsLocalAtSource
      ((@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.LocallyQuasiFinite) :
        CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType
