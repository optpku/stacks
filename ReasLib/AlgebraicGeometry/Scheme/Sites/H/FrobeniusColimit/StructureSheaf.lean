module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.FrobeniusColimit
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AbsoluteWeakNormalization.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.FrobeniusColimit

/-!
# Structure sheaf map to the Frobenius-colimit h-sheaf

This module relates the structure presheaf on a chosen big h site to the h-sheaf
obtained from its sectionwise Frobenius colimit.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit

/-- The canonical morphism from the structure presheaf to the Frobenius-colimit
h-sheaf, through the initial stage of the colimit. -/
noncomputable def structureToSheaf (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    Scheme.Site.structurePresheaf (ChosenBigSite.sliceToScheme Schh S) ⟶
      (sheaf p Schh S).obj :=
  rawPresheafStage p Schh S 0 ≫ toSheaf p Schh S

/-- The canonical map from the structure presheaf to the Frobenius-colimit h-sheaf
exhibits the latter as a sheafification for the chosen big h topology. -/
theorem structureToSheaf_isSheafification (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    Presheaf.IsSheafification (bigTopology Schh S)
      (structureToSheaf p Schh S) := sorry

end AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit
