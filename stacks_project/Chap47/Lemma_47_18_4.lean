/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.LocalDuality
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DerivedCategory
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/- Lemma 47.18.4: for a coherent derived `A`-module `K`, the maximal-ideal-adic
completion of `Ext_A^{-i}(K, ω)` is isomorphic to the `A`-linear dual into `E` of
the `i`-th local cohomology module of `K`. -/
@[stacks 0AAK] #check (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.completedExtIsoLocalCohomologyDual :
    ∀ (A E : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup E] [Module A E] [Module.Injective A E]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
    (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓZ : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓZ)
    (K : D[ModuleCat.isFG A]) (i : ℤ),
    IsIsomorphic
      (ModuleCat.of A
        (AdicCompletion (IsLocalRing.maximalIdeal A)
          ((homologyFunctor (ModuleCat A) (-i)).obj
            (InternalHom.RHom.obj K.obj ω))))
      (ModuleCat.of A
        (((homologyFunctor (ModuleCat A) i).obj (RΓZ.obj K.obj).obj) →ₗ[A] E)))

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
