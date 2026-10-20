module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.BaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality.Perfect

@[expose] public section

noncomputable section

open CategoryTheory
open DerivedCategory
open DerivedTensor.Right.Monoidal
open InternalHom.TensorLeft

universe u

namespace CategoryTheory.ModuleCat

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} R))]
variable [BraidedCategory (DerivedCategory (ModuleCat.{u} R))]

/-- The trivial-duality base-change morphism is an isomorphism exactly when the
corresponding tensor-left derived internal-Hom comparison is an isomorphism. -/
theorem trivialDualityBaseChangeMap_isIso_iff_tensorLeftComparison
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} R)))
    (T : Model)
    (K : DerivedCategory (ModuleCat.{u} R))
    (h : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')) :
    IsIso (trivialDualityBaseChangeMap K h) ↔
      IsIso (comparisonOf H T
        (ModuleCat.single0 (ModuleCat.of R R')) K
        (ModuleCat.single0 (ModuleCat.of R A))) := sorry

/-- If `A` is pseudo-coherent over `R`, `R'` has finite Tor dimension over `R`,
and `A` and `R'` are Tor independent over `R`, then the trivial-duality base-change
morphism is an isomorphism for every bounded-below derived object `K`. -/
theorem trivialDualityBaseChangeMap_isIso_of_finiteTorDimension
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} R)))
    (T : @Model (ModuleCat.{u} R) _ _ _ _ _ _ _)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hA : (ModuleCat.of R A).IsPseudoCoherent)
    (hK : ∃ n : ℤ, K.IsGE n)
    (hR' : ModuleCat.HasFiniteTorDimension R (ModuleCat.of R R'))
    (hTor : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')) :
    IsIso (trivialDualityBaseChangeMap K hTor) := sorry

end CategoryTheory.ModuleCat
