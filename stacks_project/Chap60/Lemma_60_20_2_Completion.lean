/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.PolynomialPoincare.Adic

@[expose] public section

universe u

namespace DPPolynomial.DeRham

/-- The degreewise p-adic completion of an algebraic connection's de Rham complex. -/
noncomputable abbrev completedDeRhamComplex
    {A B Ω M : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Ω] [Module B Ω] [Module A Ω] [IsScalarTower A B Ω]
    [AddCommGroup M] [Module B M]
    {D : Derivation A B Ω} {family : DifferentialOperator.DeRham.Family A B Ω}
    {conn : Connection D M} (calculus : ExteriorCalculus D family)
    (hconn : Connection.IsIntegrable conn calculus) (p : ℕ) :
    CochainComplex AddCommGrpCat ℕ :=
  Connection.completedDeRhamComplex calculus hconn p

end DPPolynomial.DeRham

end
