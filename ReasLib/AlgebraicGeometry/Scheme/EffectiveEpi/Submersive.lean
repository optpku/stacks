module

public import ReasLib.AlgebraicGeometry.Scheme.EffectiveEpi
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive
public import ReasLib.AlgebraicGeometry.AffineScheme.SectionDescent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Surjective.UniversalEffectiveEpi
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Point

/-!
# Submersive criteria for universally effective epimorphic families

This file records a criterion for an effective epimorphic family of affine schemes to remain
universally effective epimorphic after passing to the underlying schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace CategoryTheory.SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily

/-- An affine universally effective epimorphic family whose coproduct map is submersive after
every affine base change remains universally effective epimorphic after passing to schemes. -/
theorem forgetToScheme {X : AffineScheme.{u}}
    (K : Over.{u} X) [IsUniversalEffectiveEpiFamily K]
    [∀ (Y : AffineScheme.{u}) (f : Y ⟶ X),
      AlgebraicGeometry.Submersive (Limits.Sigma.desc
        (fun i : K.index ↦
          AffineScheme.forgetToScheme.map ((K.baseChange f).obj i).hom))] :
    IsUniversalEffectiveEpiFamily
      (ofArrows
        (fun i : K.index ↦ AffineScheme.forgetToScheme.obj (K.obj i).left)
        (fun i : K.index ↦ AffineScheme.forgetToScheme.map (K.obj i).hom)) := sorry

end CategoryTheory.SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily
