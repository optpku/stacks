/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Weil
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.HenselianFraction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Regular


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

/-- Evaluate a rational representative on an étale object mapping into its dense
domain, then use the canonical regular-to-meromorphic sheaf morphism. -/
def rationalRepresentativeValue (φ : PartialMap X (affineLine S))
    (U : smallEtaleSite X) (a : ofOver U.left ⟶ φ.domain.left) :
    (meromorphicFunctionSheaf X).obj.obj (op U) :=
  ((toMeromorphicFunctionSheafHom X).hom.app (op U))
    (ULift.up (coordHom ((a ≫ φ.hom).app (op U.left) (𝟙 U.left))))

/-- A rational unit is the quotient of two sections when some dense-open
representative scales the denominator section to the numerator section on every
étale object inside that same domain. This also detects the quotient when the
space has no prime divisors. -/
def IsMeromorphicSectionQuotient {L : X.Modules}
    (s t : meromorphicSections X L) (f : (RationalFunction X)ˣ) : Prop :=
  ∃ φ : PartialMap X (affineLine S), φ.toRationalMap = (f : RationalFunction X) ∧
    ∀ (U : smallEtaleSite X) (a : ofOver U.left ⟶ φ.domain.left),
      a ≫ φ.domain.hom = U.hom →
        sections.eval s (op U) =
          rationalRepresentativeValue φ U a • sections.eval t (op U)

variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The rational-function unit obtained by dividing two regular meromorphic
sections. The unique dense-open scaling characterization determines the value;
the total definition uses the unit element outside its existence branch. -/
def meromorphicSectionQuotient {L : X.Modules} [isInvertibleObject L]
    (s t : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X L t) : (RationalFunction X)ˣ :=
  let _ := hs
  let _ := ht
  @dite (RationalFunction X)ˣ
    (∃! f : (RationalFunction X)ˣ, IsMeromorphicSectionQuotient s t f)
    (Classical.propDecidable _)
    (fun h ↦ Classical.choose h.exists)
    (fun _ ↦ 1)

/-- Two regular meromorphic sections of the same invertible module have exactly
one rational-function unit satisfying their dense-open scaling equation. -/
theorem existsUnique_meromorphicSectionQuotient {L : X.Modules}
    [isInvertibleObject L] (s t : meromorphicSections X L)
    (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X L t) :
    ∃! f : (RationalFunction X)ˣ, IsMeromorphicSectionQuotient s t f := sorry

/-- The constructed rational quotient satisfies the actual section-scaling
equation on a common dense open. -/
theorem meromorphicSectionQuotient_spec {L : X.Modules} [isInvertibleObject L]
    (s t : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X L t) :
    IsMeromorphicSectionQuotient s t (meromorphicSectionQuotient s t hs ht) := sorry

/-- The dense-open quotient equation characterizes the constructed rational unit. -/
theorem isMeromorphicSectionQuotient_iff_eq {L : X.Modules} [isInvertibleObject L]
    (s t : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X L t) (f : (RationalFunction X)ˣ) :
    IsMeromorphicSectionQuotient s t f ↔ f = meromorphicSectionQuotient s t hs ht := sorry

end AlgebraicGeometry.AlgebraicSpace
