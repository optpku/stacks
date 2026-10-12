/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Remark 56.7.3: if `X` and `Y` are schemes over the common affine base
`Spec (CommRingCat.of R)` and an equivalence `F` of their coherent-module
categories is `R`-linear, then its pullback-and-tensor description can be
chosen with the scheme isomorphism defined over that base. -/
@[stacks 0GPL] #check
  (AlgebraicGeometry.Scheme.coherent_equivalence_pullback_tensor_invertible_over :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}}
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
        (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf)) F),
    ∃ (f : Y ≅ X) (L : Y.Modules),
      Scheme.Modules.Invertible L ∧
        f.hom.IsOver (Spec (CommRingCat.of R)) ∧
          ∀ 𝓕 : RingedSpace.Coh X.toRingedSpace,
            Nonempty ((F.obj 𝓕).obj ≅
              (CategoryTheory.MonoidalCategory.tensorRight L).obj
                ((Scheme.Modules.pullback f.hom).obj 𝓕.obj)))
