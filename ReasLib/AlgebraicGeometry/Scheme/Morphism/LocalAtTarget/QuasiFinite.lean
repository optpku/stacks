/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiCompact

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom.FiniteType

/-- Finite-type local quasi-finiteness of scheme morphisms is local on the target for the
fpqc precoverage. -/
instance locallyQuasiFinite_isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      ((@AlgebraicGeometry.LocallyOfFiniteType ⊓ @AlgebraicGeometry.LocallyQuasiFinite) :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.Scheme.Hom.FiniteType

namespace AlgebraicGeometry.Scheme.Hom.QuasiFinite

/-- Quasi-finiteness of scheme morphisms is local on the target for the fpqc precoverage. -/
instance isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicGeometry.Scheme.Hom.QuasiFinite :
        MorphismProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.fpqcPrecoverage := sorry

end AlgebraicGeometry.Scheme.Hom.QuasiFinite
