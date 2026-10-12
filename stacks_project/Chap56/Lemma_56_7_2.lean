/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Reconstruction
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 56.7.2: for Noetherian schemes `X` and `Y`, every equivalence between
coherent-module categories is induced, up to objectwise isomorphism, by pullback
along an isomorphism `f : Y ≅ X` followed by tensoring with an invertible module
`L` on `Y`. -/
@[stacks 0GPK] #check
  (AlgebraicGeometry.Scheme.coherent_equivalence_pullback_tensor_invertible :
    ∀ {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    [F.IsEquivalence],
    ∃ (f : Y ≅ X) (L : Y.Modules),
      Scheme.Modules.Invertible L ∧
        ∀ 𝓕 : RingedSpace.Coh X.toRingedSpace,
          Nonempty ((F.obj 𝓕).obj ≅
            (CategoryTheory.MonoidalCategory.tensorRight L).obj
              ((Scheme.Modules.pullback f.hom).obj 𝓕.obj)))
