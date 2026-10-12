/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.UniversalFiniteOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-
Lemma 37.76.8: a quasi-finite morphism of finite presentation between affine schemes admits a
finitely presented base change with a finite open part that classifies every finite open part after
affine base change.
-/
@[stacks 0F3N] #check
  (AlgebraicGeometry.Scheme.Hom.exists_universalFiniteOpen :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [IsAffine X] [IsAffine Y] [QuasiFinite f] [FinitePresentation f],
    ∃ (Yuniv : Scheme.{u}) (p : Yuniv ⟶ Y) (_ : FinitePresentation p)
      (Uuniv : (pullback f p).Opens) (_ : IsFinite (Uuniv.ι ≫ pullback.snd f p)),
      ∀ {Y' : Scheme.{u}} [IsAffine Y'] (g : Y' ⟶ Y)
        (U' : (pullback f g).Opens) [IsFinite (U'.ι ≫ pullback.snd f g)],
        ∃ (φ : Y' ⟶ Yuniv) (hφ : φ ≫ p = g),
          let k := pullback.map f g f p (𝟙 X) φ (𝟙 Y)
            ((Category.comp_id f).trans (Category.id_comp f).symm)
            ((Category.comp_id g).trans hφ.symm)
          k ⁻¹ᵁ Uuniv = U')

end AlgebraicGeometry.Scheme.Hom
