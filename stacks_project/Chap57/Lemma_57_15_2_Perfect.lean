/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap57.Lemma_57_8_2_FourierMukai
public import stacks_project.Chap57.Lemma_57_8_4
public import stacks_project.Chap57.Lemma_57_14_1_Category

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- Smoothness of a Fourier--Mukai object is the smoothness of its structure morphism. -/
instance FourierMukaiObject.instSmooth {S : Scheme.{u}} (X : FourierMukaiObject S) :
    Smooth X.hom :=
  X.smooth

/-- Properness of a Fourier--Mukai object is the properness of its structure morphism. -/
instance FourierMukaiObject.instIsProper {S : Scheme.{u}} (X : FourierMukaiObject S) :
    IsProper X.hom :=
  X.proper

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- A perfect kernel induces an ambient Fourier--Mukai functor preserving perfect
objects when `X ⟶ S` is proper, flat, and of finite presentation (Lemma 57.8.4). -/
theorem mapsToPerfect {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Scheme.Hom.FinitePresentation f] [Flat f] [IsProper f]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace) :
    RingedSpace.ModuleDerived.perfect (X := X.toRingedSpace) ≤
      (RingedSpace.ModuleDerived.perfect (X := Y.toRingedSpace)).inverseImage
        (functor f g K.obj) := sorry

/-- The Fourier--Mukai transform associated to a perfect kernel, restricted to
perfect objects. -/
noncomputable def perfect {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Scheme.Hom.FinitePresentation f] [Flat f] [IsProper f]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace) :
    @RingedSpace.ModuleDerived.Perfect X.toRingedSpace ⥤
      @RingedSpace.ModuleDerived.Perfect Y.toRingedSpace :=
  ObjectProperty.FullSubcategory.restrict (functor f g K.obj) (mapsToPerfect f g K)

/-- The restricted transform agrees with the ambient Fourier--Mukai transform after
inclusion of perfect objects. -/
noncomputable def perfect_comp_inclusionIso {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S)
    [Scheme.Hom.FinitePresentation f] [Flat f] [IsProper f]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace) :
    perfect f g K ⋙ RingedSpace.ModuleDerived.Perfect.ι ≅
      RingedSpace.ModuleDerived.Perfect.ι ⋙ functor f g K.obj :=
  ObjectProperty.FullSubcategory.restrict.compιIso (functor f g K.obj)
    (mapsToPerfect f g K)

end AlgebraicGeometry.Scheme.FourierMukai
