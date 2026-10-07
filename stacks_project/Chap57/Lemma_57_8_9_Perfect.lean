module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap57.Lemma_57_8_2_FourierMukai
public import stacks_project.Chap57.Lemma_57_8_4
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- A perfect kernel over a Noetherian base induces an ambient Fourier--Mukai functor
preserving perfect objects when both structure maps are proper and flat. -/
theorem mapsToPerfect_noetherian {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [Flat f] [IsProper g] [Flat g]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace) :
    RingedSpace.ModuleDerived.perfect (X := X.toRingedSpace) ≤
      (RingedSpace.ModuleDerived.perfect (X := Y.toRingedSpace)).inverseImage
        (functor f g K.obj) := sorry

/-- The Fourier--Mukai transform associated to a perfect kernel, restricted to
perfect objects, under the Noetherian proper-and-flat hypotheses of Lemma 57.8.9. -/
noncomputable def perfectNoetherian {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [Flat f] [IsProper g] [Flat g]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace) :
    @RingedSpace.ModuleDerived.Perfect X.toRingedSpace ⥤
      @RingedSpace.ModuleDerived.Perfect Y.toRingedSpace :=
  ObjectProperty.FullSubcategory.restrict (functor f g K.obj)
    (mapsToPerfect_noetherian f g K)

/-- The restricted Noetherian transform agrees with the ambient Fourier--Mukai
transform after inclusion of perfect objects. -/
noncomputable def perfectNoetherian_comp_inclusionIso {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S)
    [IsNoetherian S] [IsProper f] [Flat f] [IsProper g] [Flat g]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace) :
    perfectNoetherian f g K ⋙ RingedSpace.ModuleDerived.Perfect.ι ≅
      RingedSpace.ModuleDerived.Perfect.ι ⋙ functor f g K.obj :=
  ObjectProperty.FullSubcategory.restrict.compιIso (functor f g K.obj)
    (mapsToPerfect_noetherian f g K)

end AlgebraicGeometry.Scheme.FourierMukai
