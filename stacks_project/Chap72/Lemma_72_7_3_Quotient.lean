/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Weil
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.LocallyFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.LocallyFinite

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Quotient
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.MeromorphicSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Principal

/-!
# Rational quotients of meromorphic sections

The quotient is a unit of the actual rational-function ring. Its defining equation
compares the two actual meromorphic sections on the same dense open, evaluated
on every étale object inside that open. No choice of henselian generator enters
this equation; the section orders continue to use the imported henselian owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite PresheafOfModules
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The principal Weil divisor of a rational unit. -/
abbrev WeilDivisor.ofRationalUnit (f : (RationalFunction X)ˣ) : WeilDivisor X :=
  principalWeilDivisor X f

#check (AlgebraicGeometry.AlgebraicSpace.principalWeilDivisor_coeff :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsIntegral X]
    (f : (RationalFunction X)ˣ) (Z : PrimeDivisor X),
    (principalWeilDivisor X f).coeff Z = Z.ord f)

#check (AlgebraicGeometry.AlgebraicSpace.meromorphicSectionQuotient_spec :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsIntegral X] {L : X.Modules} [isInvertibleObject L]
    (s t : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X L t),
    IsMeromorphicSectionQuotient s t (meromorphicSectionQuotient s t hs ht))

end AlgebraicGeometry.AlgebraicSpace
