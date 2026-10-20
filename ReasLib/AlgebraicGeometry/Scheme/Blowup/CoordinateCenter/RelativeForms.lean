/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.CoordinateCenter
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalProjectiveBundle
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ExteriorPower.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic

/-!
# Relative differential forms on coordinate-center blowups

This file records the canonical pushforward comparisons of relative differential forms for
the blowup of affine space along a coordinate center, together with the derived restriction
map from the blowup to the exceptional divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Blowup.CoordinateCenter

/-- Commutativity of the structure square for a coordinate-center blowup over `Spec R`. -/
theorem blowupSquare_w
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))) :
    π.hom ≫ Spec.map
        (CommRingCat.ofHom
          (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)))) =
      (π.hom ≫ Spec.map
          (CommRingCat.ofHom
            (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))) ≫
        𝟙 _ := sorry

/-- The structure square for a coordinate-center blowup over `Spec R`. -/
theorem blowupSquare
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))) :
    CommSq π.hom
      (π.hom ≫ Spec.map
        (CommRingCat.ofHom
          (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)))))
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)))))
      (𝟙 _) := sorry

/-- Commutativity of the square formed by the exceptional immersion, the blowup map, and the
exceptional projection to the coordinate center. -/
theorem exceptionalInclusionSquare_w
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))) :
    π.exceptionalDivisor.subschemeι ≫
        (π.hom ≫ Spec.map
          (CommRingCat.ofHom
            (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))) =
      ((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
          (Scheme.idealSheafDataOfIdealOnSpec
              (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
          Spec.map
            (CommRingCat.ofHom
              (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))) ≫
        𝟙 _ := sorry

/-- The square formed by the exceptional immersion, the blowup map, and the exceptional
projection to the coordinate center. -/
theorem exceptionalInclusionSquare
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))) :
    CommSq π.exceptionalDivisor.subschemeι
      ((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
        (Scheme.idealSheafDataOfIdealOnSpec
            (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)))))
      (π.hom ≫ Spec.map
        (CommRingCat.ofHom
          (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)))))
      (𝟙 _) := sorry

/-- Commutativity of the structure square for the exceptional projection to the coordinate
center. -/
theorem exceptionalProjectionSquare_w
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))) :
    (@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
        ((Scheme.idealSheafDataOfIdealOnSpec
            (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
          Spec.map
            (CommRingCat.ofHom
              (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))) =
      ((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
          (Scheme.idealSheafDataOfIdealOnSpec
              (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
          Spec.map
            (CommRingCat.ofHom
              (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))) ≫
        𝟙 _ := sorry

/-- The structure square for the exceptional projection to the coordinate center. -/
theorem exceptionalProjectionSquare
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))) :
    CommSq
      (@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup)
      ((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
        (Scheme.idealSheafDataOfIdealOnSpec
            (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)))))
      ((Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)))))
      (𝟙 _) := sorry

/-- The derived pullback-pushforward adjunction exists for a chosen coordinate-center blowup
morphism. -/
theorem blowupDerivedAdjunctionHasPair
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))) :
    RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom π.hom.toShHom) := sorry

/-- The derived pullback-pushforward adjunction exists for the coordinate-center immersion. -/
theorem centerInclusionDerivedAdjunctionHasPair
    (R : Type u) [CommRing R] (m n : ℕ) :
    RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι.toShHom) := sorry

/-- The derived pullback-pushforward adjunction exists for the exceptional immersion in the
coordinate-center blowup setup. -/
theorem exceptionalInclusionDerivedAdjunctionHasPair
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))) :
    RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom π.exceptionalDivisor.subschemeι.toShHom) := sorry

/-- The derived pullback-pushforward adjunction exists for the exceptional projection in the
coordinate-center blowup setup. -/
theorem exceptionalProjectionDerivedAdjunctionHasPair
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))) :
    RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup).toShHom) := sorry

/-- The derived pullback-pushforward adjunction exists for the composite of the exceptional
immersion with the coordinate-center blowup morphism. -/
theorem exceptionalInclusionBlowupCompositeDerivedAdjunctionHasPair
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))) :
    RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        (π.exceptionalDivisor.subschemeι.toShHom ≫ π.hom.toShHom)) := sorry

/-- The derived pullback-pushforward adjunction exists for the composite of the exceptional
projection with the coordinate-center immersion. -/
theorem exceptionalProjectionCenterCompositeDerivedAdjunctionHasPair
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))) :
    RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom
        ((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup).toShHom ≫
          (Scheme.idealSheafDataOfIdealOnSpec
            (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι.toShHom)) := sorry

/-- Equality of the two derived pushforward objects obtained from the exceptional square. -/
theorem exceptionalCompositeDerivedPushforward_eq
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (a : ℕ) :
    (RingedSpace.moduleDerivedPushforward
        (π.exceptionalDivisor.subschemeι.toShHom ≫ π.hom.toShHom)).obj
      ((DerivedCategory.singleFunctor π.exceptionalDivisor.subscheme.Modules 0).obj
        (Λ[a] Ω[((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
          (Scheme.idealSheafDataOfIdealOnSpec
              (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
          Spec.map
            (CommRingCat.ofHom
              (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom])) =
      (RingedSpace.moduleDerivedPushforward
        ((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup).toShHom ≫
          (Scheme.idealSheafDataOfIdealOnSpec
            (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι.toShHom)).obj
        ((DerivedCategory.singleFunctor π.exceptionalDivisor.subscheme.Modules 0).obj
          (Λ[a] Ω[((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
            (Scheme.idealSheafDataOfIdealOnSpec
                (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
            Spec.map
              (CommRingCat.ofHom
                (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom])) := sorry

/-- The derived restriction comparison from forms on the coordinate-center blowup to the
iterated derived pushforward of forms on its exceptional divisor. -/
noncomputable def exceptionalRestrictionDerivedComparison
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (a : ℕ) :
    (RingedSpace.moduleDerivedPushforward π.hom.toShHom).obj
        ((DerivedCategory.singleFunctor π.scheme.Modules 0).obj
          (Λ[a] Ω[(π.hom ≫ Spec.map
            (CommRingCat.ofHom
              (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom])) ⟶
      (RingedSpace.moduleDerivedPushforward
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι.toShHom).obj
        ((RingedSpace.moduleDerivedPushforward
          (@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup).toShHom).obj
          ((DerivedCategory.singleFunctor π.exceptionalDivisor.subscheme.Modules 0).obj
            (Λ[a] Ω[((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
              (Scheme.idealSheafDataOfIdealOnSpec
                  (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
              Spec.map
                (CommRingCat.ofHom
                  (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom]))) :=
  (RingedSpace.moduleDerivedPushforward π.hom.toShHom).map
      (RingedSpace.moduleDerivedPushforward.comparison
        π.exceptionalDivisor.subschemeι.toShHom
        (Λ[a] Ω[(π.hom ≫ Spec.map
          (CommRingCat.ofHom
            (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom])
        (Λ[a] Ω[((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
          (Scheme.idealSheafDataOfIdealOnSpec
              (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
          Spec.map
            (CommRingCat.ofHom
              (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom])
        (Scheme.RelativeDifferentials.pushforwardComparison
          (exceptionalInclusionSquare R m n π) a)) ≫
    (@RingedSpace.moduleDerivedPushforward.Composition.iso _ _ _
      π.exceptionalDivisor.subschemeι.toShHom π.hom.toShHom
      _ _ _ _ _ _ _ _ _
      (exceptionalInclusionDerivedAdjunctionHasPair R m n π)
      (blowupDerivedAdjunctionHasPair R m n π)
      (exceptionalInclusionBlowupCompositeDerivedAdjunctionHasPair R m n π)
      (RingedSpace.modulePullbackDerived.compComparison_isIso
        π.exceptionalDivisor.subschemeι.toShHom π.hom.toShHom)).hom.app
        ((DerivedCategory.singleFunctor π.exceptionalDivisor.subscheme.Modules 0).obj
          (Λ[a] Ω[((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
            (Scheme.idealSheafDataOfIdealOnSpec
                (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
            Spec.map
              (CommRingCat.ofHom
                (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom])) ≫
    eqToHom (exceptionalCompositeDerivedPushforward_eq R m n π a) ≫
    (@RingedSpace.moduleDerivedPushforward.Composition.comparison _ _ _
      (@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup).toShHom
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι.toShHom
      _ _ _ _ _ _ _ _ _
      (exceptionalProjectionDerivedAdjunctionHasPair R m n π)
      (centerInclusionDerivedAdjunctionHasPair R m n)
      (exceptionalProjectionCenterCompositeDerivedAdjunctionHasPair R m n π)
      (RingedSpace.modulePullbackDerived.compComparison_isIso
        (@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup).toShHom
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι.toShHom)).app
      ((DerivedCategory.singleFunctor π.exceptionalDivisor.subscheme.Modules 0).obj
        (Λ[a] Ω[((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
          (Scheme.idealSheafDataOfIdealOnSpec
              (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
          Spec.map
            (CommRingCat.ofHom
              (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom]))

/-- The exceptional restriction comparison is the composite of restriction, the two canonical
derived-pushforward composition comparisons, and transport across the exceptional square. -/
theorem exceptionalRestrictionDerivedComparison_def
    (R : Type u) [CommRing R] (m n : ℕ)
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (a : ℕ) :
    exceptionalRestrictionDerivedComparison R m n π a =
      (RingedSpace.moduleDerivedPushforward π.hom.toShHom).map
          (RingedSpace.moduleDerivedPushforward.comparison
            π.exceptionalDivisor.subschemeι.toShHom
            (Λ[a] Ω[(π.hom ≫ Spec.map
              (CommRingCat.ofHom
                (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom])
            (Λ[a] Ω[((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
              (Scheme.idealSheafDataOfIdealOnSpec
                  (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
              Spec.map
                (CommRingCat.ofHom
                  (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom])
            (Scheme.RelativeDifferentials.pushforwardComparison
              (exceptionalInclusionSquare R m n π) a)) ≫
        (@RingedSpace.moduleDerivedPushforward.Composition.iso _ _ _
          π.exceptionalDivisor.subschemeι.toShHom π.hom.toShHom
          _ _ _ _ _ _ _ _ _
          (exceptionalInclusionDerivedAdjunctionHasPair R m n π)
          (blowupDerivedAdjunctionHasPair R m n π)
          (exceptionalInclusionBlowupCompositeDerivedAdjunctionHasPair R m n π)
          (RingedSpace.modulePullbackDerived.compComparison_isIso
            π.exceptionalDivisor.subschemeι.toShHom π.hom.toShHom)).hom.app
            ((DerivedCategory.singleFunctor π.exceptionalDivisor.subscheme.Modules 0).obj
              (Λ[a] Ω[((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
                (Scheme.idealSheafDataOfIdealOnSpec
                    (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
                Spec.map
                  (CommRingCat.ofHom
                    (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom])) ≫
        eqToHom (exceptionalCompositeDerivedPushforward_eq R m n π a) ≫
        (@RingedSpace.moduleDerivedPushforward.Composition.comparison _ _ _
          (@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup).toShHom
          (Scheme.idealSheafDataOfIdealOnSpec
            (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι.toShHom
          _ _ _ _ _ _ _ _ _
          (exceptionalProjectionDerivedAdjunctionHasPair R m n π)
          (centerInclusionDerivedAdjunctionHasPair R m n)
          (exceptionalProjectionCenterCompositeDerivedAdjunctionHasPair R m n π)
          (RingedSpace.modulePullbackDerived.compComparison_isIso
            (@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup).toShHom
            (Scheme.idealSheafDataOfIdealOnSpec
              (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι.toShHom)).app
          ((DerivedCategory.singleFunctor π.exceptionalDivisor.subscheme.Modules 0).obj
            (Λ[a] Ω[((@IsBlowup.exceptionalProjection _ _
        (Scheme.idealSheafDataOfIdealOnSpec
          (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R)))
        π.hom π.isBlowup) ≫
              (Scheme.idealSheafDataOfIdealOnSpec
                  (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))).subschemeι ≫
              Spec.map
                (CommRingCat.ofHom
                  (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom])) := sorry


/-- For every degree `a`, the canonical map from relative `a`-forms on affine space to the
direct image of relative `a`-forms on its coordinate-center blowup is an isomorphism. -/
theorem formPushforwardComparison_isIso
    (R : Type u) [CommRing R] (m n : ℕ) [NeZero n]
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (a : ℕ) :
    IsIso (Scheme.RelativeDifferentials.pushforwardComparison
      (blowupSquare R m n π) a) := sorry

/-- For every degree `a`, the canonical map from relative `a`-forms on the coordinate center
to the direct image of relative `a`-forms on the exceptional divisor is an isomorphism. -/
theorem exceptionalFormPushforwardComparison_isIso
    (R : Type u) [CommRing R] (m n : ℕ) [NeZero n]
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (a : ℕ) :
    IsIso (Scheme.RelativeDifferentials.pushforwardComparison
      (exceptionalProjectionSquare R m n π) a) := sorry

/-- In every positive cohomological degree `q`, the restriction map from the derived direct
image of relative `a`-forms on the blowup to the iterated derived direct image from the
exceptional divisor is an isomorphism on cohomology sheaves. -/
theorem exceptionalRestrictionCohomologyMap_isIso
    (R : Type u) [CommRing R] (m n : ℕ) [NeZero n]
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (a q : ℕ) [NeZero q] :
    IsIso ((DerivedCategory.homologyFunctor
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R)))).Modules
      (q : ℤ)).map (exceptionalRestrictionDerivedComparison R m n π a)) := sorry

end AlgebraicGeometry.Blowup.CoordinateCenter
