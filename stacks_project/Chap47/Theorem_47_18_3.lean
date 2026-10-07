module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.LocalDuality
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DerivedCategory

noncomputable section

universe u

/- Theorem 47.18.3 -/
@[stacks 0A84] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.localDuality :
    ∀ (A E : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [AddCommGroup E] [Module A E] [Module.Injective A E]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A))
      (hω : ω.IsNormalizedDualizingComplex H)
      (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull)
      (RΓZ : DerivedCategory (ModuleCat A) ⥤
        IdealPowerTorsion (IsLocalRing.maximalIdeal A))
      (hRΓZ : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓZ)
      (K : DerivedCategory (ModuleCat A)),
      Nonempty
        (derivedCompletionOf (IsLocalRing.maximalIdeal A)
            (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A))
            (InternalHom.RHom.obj K ω) ≅
          InternalHom.RHom.obj (RΓZ.obj K).obj
            (ModuleCat.single0 (ModuleCat.of A E))))
