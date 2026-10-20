/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Kunneth.Complex

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Kunneth

variable {S X : Scheme.{u}}

/- This bridge exposes the reusable relative operator de Rham complex API. -/
#check (operatorComplex : ∀ {S X : Scheme.{u}} (a : X ⟶ S),
  CochainComplex (Scheme.Hom.FiniteOrderDifferentialOperatorCat a) ℕ)

#check (operatorDeRhamIso : ∀ {S X : Scheme.{u}} (a : X ⟶ S),
  (Scheme.Hom.FiniteOrderDifferentialOperatorCat.toCoefficientComplex a).obj
      (extendedOperatorComplex a) ≅
    (RingedSpace.DeRham.complex a.toLRSHom.toShHom).extend embeddingUpNat)

end AlgebraicGeometry.Scheme.DeRham.Kunneth
