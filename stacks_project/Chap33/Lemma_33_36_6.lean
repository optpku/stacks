/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Properties

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/-!
# Lemma 33.36.6 compatibility entry point

The reusable relative-Frobenius universal-homeomorphism, integrality, and
residue-field property instances are owned by
`ReasLib.AlgebraicGeometry.Scheme.Frobenius.Properties`.
-/

/- Lemma 33.36.6: if `S` has prime characteristic `p`, then the relative Frobenius of
`f : X ⟶ S` is a universal homeomorphism, is integral, and induces purely inseparable
residue field extensions. -/
@[stacks 0CCB]
#check (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_universalHomeomorphism :
  ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.IsCharP S p],
    UniversalHomeomorphism (Scheme.Hom.relativeFrobenius (p := p) f))

#check (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_isIntegralHom :
  ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.IsCharP S p],
    IsIntegralHom (Scheme.Hom.relativeFrobenius (p := p) f))

#check (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_residueField_isPurelyInseparable :
  ∀ {p : ℕ} [Fact p.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.IsCharP S p] (x : X),
    IsPurelyInseparable
      ((Scheme.Hom.relativeFrobeniusTarget (p := p) f).residueField
        ((Scheme.Hom.relativeFrobenius (p := p) f) x))
      (X.residueField x))
