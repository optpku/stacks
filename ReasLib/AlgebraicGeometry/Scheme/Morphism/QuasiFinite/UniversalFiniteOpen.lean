module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite

/-!
# Universal finite opens of quasi-finite morphisms

A quasi-finite morphism of finite presentation between affine schemes admits a finitely presented
parameter scheme carrying a finite open that classifies finite opens after affine base change.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A quasi-finite morphism of finite presentation between affine schemes admits a finitely
presented base change with a finite open part that classifies every finite open part after affine
base change. -/
@[stacks 0F3N]
theorem exists_universalFiniteOpen {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y] [QuasiFinite f] [FinitePresentation f] :
    ∃ (Yuniv : Scheme.{u}) (p : Yuniv ⟶ Y) (_ : FinitePresentation p)
      (Uuniv : (pullback f p).Opens) (_ : IsFinite (Uuniv.ι ≫ pullback.snd f p)),
      ∀ {Y' : Scheme.{u}} [IsAffine Y'] (g : Y' ⟶ Y)
        (U' : (pullback f g).Opens) [IsFinite (U'.ι ≫ pullback.snd f g)],
        ∃ (φ : Y' ⟶ Yuniv) (hφ : φ ≫ p = g),
          let k := pullback.map f g f p (𝟙 X) φ (𝟙 Y)
            ((Category.comp_id f).trans (Category.id_comp f).symm)
            ((Category.comp_id g).trans hφ.symm)
          k ⁻¹ᵁ Uuniv = U' := sorry

end AlgebraicGeometry.Scheme.Hom
