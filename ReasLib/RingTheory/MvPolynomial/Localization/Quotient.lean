/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Ideal.Over
public import ReasLib.RingTheory.Localization.Away.Iterated
public import ReasLib.RingTheory.MvPolynomial.Localization

@[expose] public section

/-!
# Quotient charts after iterated coefficient localizations

This leaf owns the presentation-independent quotient chart obtained by first
localizing a multivariate polynomial coefficient ring away from `f` and then
away from the image of `g`.  Mathlib already provides the general fact that
localization commutes with quotienting; the declarations here package its
canonical coefficient-polynomial specialization and the direct final chart.
-/

universe u v

namespace MvPolynomial.Localization.Iterated

variable {σ : Type u} {R : Type v} [CommRing R]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Tag `051T`: after localizing coefficients from `R_f` to `R_(f * g)`, the
quotient by the mapped polynomial ideal is the localization of the original
quotient away from the class of `C g`. -/
@[stacks 051T "iterated coefficient-localization quotient owner"]
theorem quotientIsLocalization (f g : R)
    (K : Ideal (MvPolynomial σ (Localization.Away f))) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial σ (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let ρfg : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (MvPolynomial σ (Localization.Away f))
        (MvPolynomial σ (Localization.Away fg)) := (MvPolynomial.map ρfg).toAlgebra
    let Kfg : Ideal (MvPolynomial σ (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfg) K
    let Tfg := MvPolynomial σ (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    IsLocalization.Away uQ Tfg := sorry

/-- Tag `051T`: the quotient induced by the iterated coefficient map is an
`R_f`-algebra tower through the original polynomial quotient. -/
@[stacks 051T "iterated coefficient-localization quotient scalar tower"]
theorem quotientIsScalarTower (f g : R)
    (K : Ideal (MvPolynomial σ (Localization.Away f))) :
    let fg : R := f * g
    let Qf := MvPolynomial σ (Localization.Away f) ⧸ K
    let ρfg : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) :=
      Localization.Away.Iterated.rightAlgebra f g
    letI : Algebra (MvPolynomial σ (Localization.Away f))
        (MvPolynomial σ (Localization.Away fg)) := (MvPolynomial.map ρfg).toAlgebra
    let Kfg : Ideal (MvPolynomial σ (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfg) K
    let Tfg := MvPolynomial σ (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
    IsScalarTower (Localization.Away f) Qf Tfg := sorry

/-- Tag `051T`: the canonical final chart for an iterated coefficient-away
localization of a multivariate-polynomial quotient. -/
@[stacks 051T "iterated coefficient-localization quotient chart"]
noncomputable def quotientAlgEquiv (f g : R)
    (K : Ideal (MvPolynomial σ (Localization.Away f))) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial σ (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let ρfg : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) :=
      Localization.Away.Iterated.rightAlgebra f g
    letI : Algebra (MvPolynomial σ (Localization.Away f))
        (MvPolynomial σ (Localization.Away fg)) := (MvPolynomial.map ρfg).toAlgebra
    let Kfg : Ideal (MvPolynomial σ (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfg) K
    let Tfg := MvPolynomial σ (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
    Localization.Away uQ ≃ₐ[Localization.Away f] Tfg :=
  let fg : R := f * g
  let c : Localization.Away f := algebraMap R (Localization.Away f) g
  let Qf := MvPolynomial σ (Localization.Away f) ⧸ K
  let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
  let ρfg : Localization.Away f →+* Localization.Away fg :=
    IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
  -- Local instance justification (instance diamond): select the iterated-away coefficient action.
  letI : Algebra (Localization.Away f) (Localization.Away fg) :=
    Localization.Away.Iterated.rightAlgebra f g
  -- Local instance justification (proof-local temporary data): lift the coefficient map to polynomials.
  letI : Algebra (MvPolynomial σ (Localization.Away f))
      (MvPolynomial σ (Localization.Away fg)) := (MvPolynomial.map ρfg).toAlgebra
  let Kfg : Ideal (MvPolynomial σ (Localization.Away fg)) :=
    Ideal.map (MvPolynomial.map ρfg) K
  let Tfg := MvPolynomial σ (Localization.Away fg) ⧸ Kfg
  -- Local instance justification (proof-local temporary data): descend the polynomial map to quotients.
  letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
  -- Local instance justification (instance diamond): use the coefficient action induced on the quotient.
  letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
  -- Local instance justification (search instability): pin the canonical source localization tower.
  letI : IsScalarTower (Localization.Away f) Qf (Localization.Away uQ) :=
    inferInstance
  -- Local instance justification (proof-local temporary data): use the named target quotient tower.
  letI : IsScalarTower (Localization.Away f) Qf Tfg :=
    quotientIsScalarTower (σ := σ) f g K
  -- Local instance justification (proof-local temporary data): expose the target localization property.
  letI : IsLocalization.Away uQ Tfg :=
    quotientIsLocalization (σ := σ) f g K
  (Localization.algEquiv (Submonoid.powers uQ) Tfg).restrictScalars
    (Localization.Away f)

/-- Tag `051T`: the final quotient chart sends the localization class of a
polynomial to the class of its coefficient-wise image in `R_(f * g)`. -/
@[stacks 051T "iterated coefficient-localization quotient generator"]
theorem quotientAlgEquiv_apply_mk (f g : R)
    (K : Ideal (MvPolynomial σ (Localization.Away f)))
    (ψ : MvPolynomial σ (Localization.Away f)) :
    let fg : R := f * g
    let c : Localization.Away f := algebraMap R (Localization.Away f) g
    let Qf := MvPolynomial σ (Localization.Away f) ⧸ K
    let uQ : Qf := Ideal.Quotient.mk K (MvPolynomial.C c)
    let ρfg : Localization.Away f →+* Localization.Away fg :=
      IsLocalization.Away.awayToAwayRight (P := Localization.Away fg) f g
    letI : Algebra (Localization.Away f) (Localization.Away fg) :=
      Localization.Away.Iterated.rightAlgebra f g
    letI : Algebra (MvPolynomial σ (Localization.Away f))
        (MvPolynomial σ (Localization.Away fg)) := (MvPolynomial.map ρfg).toAlgebra
    let Kfg : Ideal (MvPolynomial σ (Localization.Away fg)) :=
      Ideal.map (MvPolynomial.map ρfg) K
    let Tfg := MvPolynomial σ (Localization.Away fg) ⧸ Kfg
    letI : Algebra Qf Tfg := Ideal.Quotient.algebraQuotientMapQuotient
    letI : Algebra (Localization.Away f) Tfg := Ideal.Quotient.algebra _
    quotientAlgEquiv (σ := σ) f g K
        (Localization.mk (Ideal.Quotient.mk K ψ) 1) =
      Ideal.Quotient.mk Kfg (MvPolynomial.map ρfg ψ) := sorry

end MvPolynomial.Localization.Iterated
