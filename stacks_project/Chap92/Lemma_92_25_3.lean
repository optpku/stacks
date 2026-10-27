/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.DerivedPullback
public import ReasLib.AlgebraicGeometry.Scheme.CotangentSite.NaiveDifferentials
import StacksCheckRecall

/-!
# The cotangent complex of a scheme over a ring via `Lπ_!`

Lemma 92.25.3 identifies `L_{X / Λ}` in `D(O_X)` with
`Lπ_!(Li^* Ω_{O / underline{Λ}}) = Lπ_!(i^* Ω_{O / underline{Λ}}) =
Lπ_!(Ω_{O / underline{Λ}} ⊗_O underline{O}_X)`, computed by the fibrewise
standard polynomial resolution of Remark 92.25.2.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 92.25.3. In the situation above there is a canonical isomorphism
`L_{X / Λ} ≅ Lπ_!(Li^* Ω) ≅ Lπ_!(i^* Ω) ≅ Lπ_!(Ω ⊗_O underline{O}_X)`
in `D(O_X)`, represented by `cotangentLowerShriekIso` and `lowerShriekOmega`.
The source chain `Li^* omegaSheaf = i^* omegaSheaf = omegaPullback` is
recorded by `derivedPullbackIso`, the flatness isomorphism
`derivedInverseImage.obj (singleFunctor.obj omegaSheaf) ≅
singleFunctor.obj omegaPullback` in `D(underline{O}_X)`. `O` is polynomial
(hence `omegaSheaf` is `O`-flat) on every object of `C_{X/Λ}`.
`lowerShriekOmega` is the sheafification of `U ↦ L_{O_X(U) / Λ}`, which is
`L_{O_X / underline{Λ}}` by Remark 92.18.5 and equals `L_{X / Λ}` by
Lemma 92.24.3. -/
@[stacks 08T9] #check (AlgebraicGeometry.Scheme.CotangentSite.cotangentLowerShriekIso :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)],
    DerivedCategory.Q.obj (Hom.cotangentComplex (X ↘ Spec Λ)) ≅
      AlgebraicGeometry.Scheme.CotangentSite.lowerShriekOmega Λ X)

/- The forward map of `cotangentLowerShriekIso` is `overRingIso` followed by the inverse
of the derived evaluation comparison. -/
#check (AlgebraicGeometry.Scheme.CotangentSite.cotangentLowerShriekIso_hom :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)],
    (AlgebraicGeometry.Scheme.CotangentSite.cotangentLowerShriekIso Λ X).hom =
      (Cotangent.overRingIso Λ X).hom ≫
        inv (AlgebraicGeometry.Scheme.CotangentSite.omegaEvalToConstCotangentDerived Λ X))

#check (AlgebraicGeometry.Scheme.CotangentSite.derivedPullbackIso :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)],
    (AlgebraicGeometry.Scheme.CotangentSite.derivedInverseImage Λ X).obj
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u + 1}
            (AlgebraicGeometry.Scheme.CotangentSite.structureSheaf Λ X)) (0 : ℤ)).obj
        (AlgebraicGeometry.Scheme.CotangentSite.omegaSheaf Λ X)) ≅
    (DerivedCategory.singleFunctor
        (SheafOfModules.{u + 1}
          (AlgebraicGeometry.Scheme.CotangentSite.inverseImageStructureSheaf Λ X)) (0 : ℤ)).obj
      (AlgebraicGeometry.Scheme.CotangentSite.omegaPullback Λ X))

#check (AlgebraicGeometry.Scheme.CotangentSite.omegaSheaf :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)],
    SheafOfModules.{u + 1} (AlgebraicGeometry.Scheme.CotangentSite.structureSheaf Λ X))

#check (AlgebraicGeometry.Scheme.CotangentSite.omegaPullback :
  ∀ (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)],
    SheafOfModules.{u + 1}
      (AlgebraicGeometry.Scheme.CotangentSite.inverseImageStructureSheaf Λ X))
