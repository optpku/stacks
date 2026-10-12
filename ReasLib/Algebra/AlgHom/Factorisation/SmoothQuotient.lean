/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.AlgHom.Factorisation

/-!
# Smooth quotient factorisations of algebra homomorphisms

This file attaches smoothness and finite generation data to a quotient
factorisation.  The construction is independent of any nilpotence or
ind-smoothness hypothesis and can therefore be imported directly by other
factorisation arguments.
-/

@[expose] public section

universe u v w

namespace AlgHom.QuotientFactorisation

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/-- A quotient factorisation whose prequotient algebra is smooth and whose
defining ideal is finitely generated inside the extension of a chosen base
ideal. -/
@[stacks 07CK "smooth quotient factorisation"]
structure Smooth (I : Ideal R) (f : A →ₐ[R] B) where
  /-- The underlying quotient factorisation. -/
  base : AlgHom.QuotientFactorisation f
  /-- Smoothness of the intermediate algebra. -/
  [smooth : Algebra.Smooth R base.prequotient]
  /-- The quotient ideal lies over the chosen base ideal. -/
  ideal_le : base.ideal ≤ I.map (algebraMap R base.prequotient)
  /-- The quotient ideal is finitely generated. -/
  ideal_fg : base.ideal.FG

attribute [instance] Smooth.smooth

namespace Smooth

variable {I : Ideal R} {f : A →ₐ[R] B}

/-- The smooth algebra before taking the quotient. -/
abbrev prequotient (F : Smooth I f) := F.base.prequotient

/-- The quotient algebra through which the original map factors. -/
abbrev mid (F : Smooth I f) := F.base.mid

/-- The finitely generated ideal defining the quotient midpoint. -/
abbrev ideal (F : Smooth I f) : Ideal F.prequotient := F.base.ideal

namespace mid

/-- The quotient midpoint is finitely presented over the base ring. -/
@[stacks 07CK "finite presentation of a smooth quotient midpoint"]
instance finitePresentation (F : Smooth I f) :
    Algebra.FinitePresentation R F.mid := sorry

end mid

/-- The source map into the quotient midpoint. -/
abbrev fromSource (F : Smooth I f) : A →ₐ[R] F.mid := F.base.fromSource

/-- The map from the quotient midpoint to the target. -/
abbrev toTarget (F : Smooth I f) : F.mid →ₐ[R] B := F.base.toTarget

/-- The quotient maps factor the original algebra homomorphism. -/
theorem factor (F : Smooth I f) :
    F.toTarget.comp F.fromSource = f := sorry

/-- Forget the smooth prequotient presentation while retaining the induced
finite-presentation factorisation. -/
noncomputable def toFinite (F : Smooth I f) : AlgHom.Factorisation.Finite f :=
  { base := F.base.toFactorisation
    finitePresentation := inferInstanceAs (Algebra.FinitePresentation R F.mid) }

/-- The finite factorisation preserves the source map. -/
@[simp]
theorem fromSource_toFinite (F : Smooth I f) :
    F.toFinite.fromSource = F.fromSource := sorry

/-- The finite factorisation preserves the target map. -/
@[simp]
theorem toTarget_toFinite (F : Smooth I f) :
    F.toFinite.toTarget = F.toTarget := sorry

/-- The smoothness, ideal conditions, and triangle law carried by a smooth
quotient factorisation. -/
@[stacks 07CK "smooth quotient factorisation specification"]
theorem spec (F : Smooth I f) :
    Algebra.Smooth R F.prequotient ∧
      F.ideal ≤ I.map (algebraMap R F.prequotient) ∧
      F.ideal.FG ∧
      F.toTarget.comp F.fromSource = f := sorry

/-- Attach smoothness and the two ideal conditions to an existing quotient
factorisation. -/
def of (F : AlgHom.QuotientFactorisation f)
    [Algebra.Smooth R F.prequotient]
    (ideal_le : F.ideal ≤ I.map (algebraMap R F.prequotient))
    (ideal_fg : F.ideal.FG) : Smooth I f :=
  { base := F
    ideal_le := ideal_le
    ideal_fg := ideal_fg }

/-- Forgetting the conditions attached by `of` recovers the original quotient
factorisation. -/
@[simp]
theorem base_of (F : AlgHom.QuotientFactorisation f)
    [Algebra.Smooth R F.prequotient]
    {ideal_le : F.ideal ≤ I.map (algebraMap R F.prequotient)}
    {ideal_fg : F.ideal.FG} :
    (of F ideal_le ideal_fg).base = F := sorry

/-- Build a smooth quotient factorisation directly from a smooth algebra, an
ideal, and the two maps through its quotient. -/
@[stacks 07CK "smooth quotient factorisation from algebra maps"]
def ofMaps {P : Type (max u v w)} [CommRing P] [Algebra R P]
    [Algebra.Smooth R P] (J : Ideal P)
    (fromSource : A →ₐ[R] P ⧸ J) (toTarget : P ⧸ J →ₐ[R] B)
    (factor : toTarget.comp fromSource = f)
    (ideal_le : J ≤ I.map (algebraMap R P)) (ideal_fg : J.FG) :
    Smooth I f :=
  { base := AlgHom.QuotientFactorisation.ofMaps J fromSource toTarget factor
    smooth := inferInstanceAs (Algebra.Smooth R P)
    ideal_le := ideal_le
    ideal_fg := ideal_fg }

/-- The underlying quotient factorisation built by `ofMaps` is the canonical
one attached to the supplied ideal and maps. -/
@[simp]
theorem base_ofMaps {P : Type (max u v w)} [CommRing P] [Algebra R P]
    [Algebra.Smooth R P] (J : Ideal P)
    (fromSource : A →ₐ[R] P ⧸ J) (toTarget : P ⧸ J →ₐ[R] B)
    {factor : toTarget.comp fromSource = f}
    {ideal_le : J ≤ I.map (algebraMap R P)} {ideal_fg : J.FG} :
    (ofMaps J fromSource toTarget factor ideal_le ideal_fg).base =
      AlgHom.QuotientFactorisation.ofMaps J fromSource toTarget factor := sorry

/-- The defining ideal of a smooth quotient factorisation built by `ofMaps`
is the supplied ideal. -/
@[simp]
theorem ideal_ofMaps {P : Type (max u v w)} [CommRing P] [Algebra R P]
    [Algebra.Smooth R P] (J : Ideal P)
    (fromSource : A →ₐ[R] P ⧸ J) (toTarget : P ⧸ J →ₐ[R] B)
    {factor : toTarget.comp fromSource = f}
    {ideal_le : J ≤ I.map (algebraMap R P)} {ideal_fg : J.FG} :
    (ofMaps J fromSource toTarget factor ideal_le ideal_fg).ideal = J := sorry

/-- The source map of a smooth quotient factorisation built by `ofMaps` is
the supplied source map. -/
@[simp]
theorem fromSource_ofMaps
    {P : Type (max u v w)} [CommRing P] [Algebra R P]
    [Algebra.Smooth R P] (J : Ideal P)
    (fromSource : A →ₐ[R] P ⧸ J) (toTarget : P ⧸ J →ₐ[R] B)
    {factor : toTarget.comp fromSource = f}
    {ideal_le : J ≤ I.map (algebraMap R P)} {ideal_fg : J.FG} :
    (ofMaps J fromSource toTarget factor ideal_le ideal_fg).fromSource =
      fromSource := sorry

/-- The target map of a smooth quotient factorisation built by `ofMaps` is
the supplied target map. -/
@[simp]
theorem toTarget_ofMaps
    {P : Type (max u v w)} [CommRing P] [Algebra R P]
    [Algebra.Smooth R P] (J : Ideal P)
    (fromSource : A →ₐ[R] P ⧸ J) (toTarget : P ⧸ J →ₐ[R] B)
    {factor : toTarget.comp fromSource = f}
    {ideal_le : J ≤ I.map (algebraMap R P)} {ideal_fg : J.FG} :
    (ofMaps J fromSource toTarget factor ideal_le ideal_fg).toTarget =
      toTarget := sorry

end Smooth

end AlgHom.QuotientFactorisation
