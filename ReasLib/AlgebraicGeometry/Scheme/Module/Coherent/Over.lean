/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Reconstruction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Linearity
public import Mathlib.AlgebraicGeometry.Over

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- An `R`-linear equivalence between coherent-module categories of Noetherian
schemes over `Spec (CommRingCat.of R)` is induced by pullback along an
isomorphism over that affine base followed by tensoring with an invertible
module. -/
theorem coherent_equivalence_pullback_tensor_invertible_over
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y]
    [X.Over (Spec (CommRingCat.of R))] [Y.Over (Spec (CommRingCat.of R))]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    [F.IsEquivalence] [F.Additive]
    (hF : @CategoryTheory.Functor.Linear R _ _ _ _ _ _ _
      (@CategoryTheory.Linear.fullSubcategory X.Modules _ _ R _
        (Scheme.Modules.baseLinear (X ↘ Spec (CommRingCat.of R)))
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf))
      (@CategoryTheory.Linear.fullSubcategory Y.Modules _ _ R _
        (Scheme.Modules.baseLinear (Y ↘ Spec (CommRingCat.of R)))
        (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)) F) :
    ∃ (f : Y ≅ X) (L : Y.Modules),
      Scheme.Modules.Invertible L ∧
        f.hom.IsOver (Spec (CommRingCat.of R)) ∧
          ∀ 𝓕 : RingedSpace.Coh X.toRingedSpace,
            Nonempty ((F.obj 𝓕).obj ≅
              (CategoryTheory.MonoidalCategory.tensorRight L).obj
                ((Scheme.Modules.pullback f.hom).obj 𝓕.obj)) := sorry

end AlgebraicGeometry.Scheme
