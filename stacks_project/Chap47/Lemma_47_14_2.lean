module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.BaseChange.InternalHom

@[expose] public section

noncomputable section

open CategoryTheory
open DerivedCategory
open DerivedTensor.Right.Monoidal

universe u

namespace CategoryTheory.ModuleCat

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} R))]
variable [BraidedCategory (DerivedCategory (ModuleCat.{u} R))]

/- Lemma 47.14.2: if `A` is pseudo-coherent over `R`, `R'` has finite Tor dimension
over `R` (for example, if `R ⟶ R'` is flat), and `A` and `R'` are Tor independent over
`R`, then the trivial-duality base-change map is an isomorphism for `K ∈ D⁺(R)`. -/
@[stacks 0BZM] #check
  (CategoryTheory.ModuleCat.trivialDualityBaseChangeMap_isIso_of_finiteTorDimension :
    ∀ (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} R)))
      (T : @Model (ModuleCat.{u} R) _ _ _ _ _ _ _)
      (K : DerivedCategory (ModuleCat.{u} R))
      (hA : (ModuleCat.of R A).IsPseudoCoherent)
      (hK : ∃ n : ℤ, K.IsGE n)
      (hR' : ModuleCat.HasFiniteTorDimension R (ModuleCat.of R R'))
      (hTor : Tor.IsIndependent (ModuleCat.of R A) (ModuleCat.of R R')),
      IsIso (trivialDualityBaseChangeMap K hTor))

end CategoryTheory.ModuleCat
