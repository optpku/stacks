module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Ph.InverseImage
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Comparison of ph and étale sheaves

The canonical comparison units are invertible on sheaves from the small étale
site. Positive higher direct images vanish for locally torsion abelian sheaves.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.PhComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PhComparison

/-- For a sheaf of sets `F` on the small étale site, the comparison unit
identifies `ε_{X,*} (a_X⁻¹ F)` with `π_X⁻¹ F`. -/
@[instance]
theorem epsilon_pushforward_aInverseImage_unit_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso ((epsilon X).adjunction.unit.app (((siteMorphismOfTopoi X)⁻¹).obj F)) := sorry

/-- For a sheaf of sets `F` on the small étale site, the comparison unit
identifies `a_{X,*} (a_X⁻¹ F)` with `F`. -/
@[instance]
theorem toSmallEtale_unit_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso ((toSmallEtale X).adjunction.unit.app F) := sorry

/-- For a locally torsion abelian sheaf `F` on the small étale site and `0 < i`,
the higher direct images `R^i ε_{X,*} (a_X⁻¹ F)` vanish. -/
theorem epsilon_rightDerived_aInverseImage_isZero {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (hF : F.IsLocallyTorsion) (i : ℕ) (hi : 0 < i) :
    IsZero
      (((comparisonTopologyPushforwardAb etale_le_ph X).rightDerived i).obj
        ((aInverseImage X).obj F)) := sorry

end AlgebraicGeometry.AlgebraicSpace.PhComparison

end

end
