module

public import stacks_project.Chap92.Lemma_92_25_3_Comparison
public import stacks_project.Chap92.Lemma_92_25_3_Omega
import Mathlib.Tactic.CrossRefAttribute

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

/-- Lemma 92.25.3. In the situation above there is a canonical isomorphism
`Hom.cotangentComplex (X ↘ Spec Λ) ≅ lowerShriekOmega Λ X` in `D(O_X)`.
The source chain `Li^* omegaSheaf = i^* omegaSheaf = omegaPullback` is
recorded by `derivedPullbackIso`, the flatness isomorphism
`derivedInverseImage.obj (singleFunctor.obj omegaSheaf) ≅
singleFunctor.obj omegaPullback` in `D(underline{O}_X)`. `O` is polynomial
(hence `omegaSheaf` is `O`-flat) on every object of `C_{X/Λ}`.
`lowerShriekOmega` is the sheafification of `U ↦ L_{O_X(U) / Λ}`, which is
`L_{O_X / underline{Λ}}` by Remark 92.18.5 and equals `L_{X / Λ}` by
Lemma 92.24.3. -/
@[stacks 08T9]
abbrev cotangentLowerShriekIso (Λ : CommRingCat.{u}) (X : Scheme.{u}) [X.Over (Spec Λ)] :
    DerivedCategory.Q.obj (Hom.cotangentComplex (X ↘ Spec Λ)) ≅
      CotangentSite.lowerShriekOmega Λ X :=
  CotangentSite.cotangentLowerShriekIso Λ X

/-- The forward map of `cotangentLowerShriekIso` is `overRingIso` followed by the inverse
of the derived evaluation comparison. -/
theorem cotangentLowerShriekIso_hom (Λ : CommRingCat.{u}) (X : Scheme.{u})
    [X.Over (Spec Λ)] :
    (cotangentLowerShriekIso Λ X).hom =
      (Cotangent.overRingIso Λ X).hom ≫
        inv (CotangentSite.omegaEvalToConstCotangentDerived Λ X) :=
  sorry
