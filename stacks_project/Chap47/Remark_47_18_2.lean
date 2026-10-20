/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap47.Lemma_47_18_1
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.Uniqueness
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.Automorphism
public import ReasLib.RingTheory.AdicCompletion.IdealPowerTorsion.Automorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.DerivedCategory

noncomputable section

universe u v

/- Remark 47.18.2 (1): the zeroth local cohomology of a normalized dualizing
complex is an injective hull of the residue field. -/
@[stacks 0A83] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.localCohomologyH0IsInjectiveHull :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A))
      (hω : ω.IsNormalizedDualizingComplex H)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤
        IdealPowerTorsion (IsLocalRing.maximalIdeal A))
      (hRΓZ : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓZ),
      let K := (RΓZ.obj ω).obj
      let E := (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj K
      ∃ (_ : Module.Injective A E)
        (ι : IsLocalRing.ResidueField A →ₗ[A] E), ι.IsInjectiveHull)

/- Remark 47.18.2 (2): the local cohomology of a normalized dualizing complex at
the closed point is concentrated in degree zero. -/
@[stacks 0A83] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.localCohomologyIsoSingleH0 :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A))
      (hω : ω.IsNormalizedDualizingComplex H)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤
        IdealPowerTorsion (IsLocalRing.maximalIdeal A))
      (hRΓZ : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓZ),
      let K := (RΓZ.obj ω).obj
      let E := (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj K
      Nonempty (K ≅ ModuleCat.single0 E))

/- Remark 47.18.2 (3): normalized dualizing complexes over a Noetherian local
ring are unique up to isomorphism. -/
@[stacks 0A83] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.nonempty_iso :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      {ω ω' : DerivedCategory (ModuleCat.{u} A)},
      ω.IsNormalizedDualizingComplex H →
        ω'.IsNormalizedDualizingComplex H → Nonempty (ω ≅ ω'))

/- Remark 47.18.2 (4): the automorphism group of a normalized dualizing complex
over `A` is identified by the canonical scalar action with `Aˣ`. -/
@[stacks 0A83] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.scalarUnitsToAut_bijective :
    ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A))
      (hω : ω.IsNormalizedDualizingComplex H),
      Function.Bijective (CategoryTheory.DerivedCategory.scalarUnitsToAut A ω))

/- Remark 47.18.2 (5): any two injective hulls of the residue field of a local
ring are linearly equivalent compatibly with their hull embeddings. -/
section

variable (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable {E E' : Type u} [AddCommGroup E] [AddCommGroup E']
variable [Module A E] [Module A E'] [Module.Injective A E] [Module.Injective A E']
variable {ι : IsLocalRing.ResidueField A →ₗ[A] E}
variable {ι' : IsLocalRing.ResidueField A →ₗ[A] E'}

@[stacks 0A83] #check
  (LinearMap.IsInjectiveHull.exists_linearEquiv
    (R := A) (M := IsLocalRing.ResidueField A) (E := E) (E' := E') (i := ι) (j := ι') :
      ι.IsInjectiveHull → ι'.IsInjectiveHull →
        ∃ e : E ≃ₗ[A] E', e.toLinearMap.comp ι = ι')

end

/- Remark 47.18.2 (6): the automorphism group of an injective hull of the
residue field is identified by its canonical action with the units of the
maximal-ideal-adic completion of `A`. -/
@[stacks 0A83] #check
  (LinearMap.IsInjectiveHull.completionUnitsToAut_bijective :
    ∀ (A : Type u) (E : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [AddCommGroup E] [Module A E] [Module.Injective A E]
      (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull),
      Function.Bijective
        (Module.IsIdealPowerTorsion.completionUnitsToAut
          (IsLocalRing.maximalIdeal A)
          (LinearMap.IsInjectiveHull.maximalIdealPowerTorsion A E ι hι)))
