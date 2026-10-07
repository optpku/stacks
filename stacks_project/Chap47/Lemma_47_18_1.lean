module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.LocalCohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.DerivedCategory

noncomputable section

universe u

/- Lemma 47.18.1 (1): the zeroth cohomology of a normalized dualizing complex
with support in the closed point is an injective hull of the residue field. -/
@[stacks 0A82] #check
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

/- Lemma 47.18.1 (2): closed-point-supported local cohomology of a normalized
dualizing complex is its zeroth cohomology module concentrated in degree zero. -/
@[stacks 0A82] #check
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
