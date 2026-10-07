module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.DimensionOne

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HigherDirectImage

/-- In a commutative triangle `X ⟶ Y ⟶ S`, if `X` is flat over `S`,
`f : X ⟶ Y` is proper with fibres of dimension at most one, and
`R¹f_*𝒪_X = 0`, then `f_*𝒪_X` is flat over `S`. -/
theorem pushforwardStructureSheaf_isFlatOver
    {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)
    (sq : CommSq f p q (𝟙 S)) [Flat p] [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
    (hR1 : IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom
      (SheafOfModules.unit X.ringCatSheaf) 1)) :
    SheafOfModules.IsFlatOver
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
      q.toShHom := sorry

/-- Under the hypotheses ensuring flatness of `f_*𝒪_X` over `S`, formation of
`f_*𝒪_X` commutes with every base change `S' ⟶ S`: for chosen cartesian
presentations of `Y' = Y ×_S S'` and `X' = X ×_Y Y'`, the canonical
base-change component is invertible. -/
theorem pushforwardStructureSheaf_baseChange_isIso
    {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)
    (sq : CommSq f p q (𝟙 S)) [Flat p] [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞))
    (hR1 : IsZero (RingedSpace.Hom.higherDirectImageModule f.toShHom
      (SheafOfModules.unit X.ringCatSheaf) 1))
    {X' Y' S' : Scheme.{u}} (g : S' ⟶ S)
    (gY : Y' ⟶ Y) (q' : Y' ⟶ S') (hY : IsPullback gY q' q g)
    (gX : X' ⟶ X) (f' : X' ⟶ Y') (hf : IsPullback gX f' f gY) :
    IsIso ((BaseChange.map
      ((hf.toCommSq.map (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace)) :
          CommSq gX.toShHom f'.toShHom f.toShHom gY.toShHom)).app
            (SheafOfModules.unit X.ringCatSheaf)) := sorry

end AlgebraicGeometry.Scheme.HigherDirectImage
