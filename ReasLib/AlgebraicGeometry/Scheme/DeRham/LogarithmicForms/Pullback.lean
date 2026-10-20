/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogarithmicForms.ChernClass
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.LogarithmicForms

variable {X' S' : Scheme.{u}} {g : X' ⟶ X} {h : X ⟶ S} {h' : X' ⟶ S'}
variable {k : S' ⟶ S}

/-- The canonical cohomology pullback maps for a commutative square, with the naturality laws
for units, logarithmic forms, and Picard classes. -/
structure ChernPullback (sq : CommSq g h' h k) where
  /-- Pullback on cohomology of units. -/
  unitsPullback : Sheaf.H.{u} (Sheaf.unitsAddSheaf X.sheaf) 1 →+
    Sheaf.H.{u} (Sheaf.unitsAddSheaf X'.sheaf) 1
  /-- Pullback on logarithmic first cohomology. -/
  logarithmicPullback : H h 1 1 →+ H h' 1 1
  /-- Pullback commutes with logarithmic `dlog`. -/
  dlog_naturality : logarithmicPullback.comp (Sheaf.H.map (dlog h) 1) =
    (Sheaf.H.map (dlog h') 1).comp unitsPullback
  /-- Pullback of the units cohomology class agrees with pullback on Picard groups. -/
  picard_naturality : unitsPullback.comp
      (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf) =
    (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X'.sheaf).comp
      (Scheme.Hom.picardPullback g)

namespace ChernPullback

/-- Build the canonical pullback comparison from its two cohomology maps and naturality
squares. -/
noncomputable def ofMaps (sq : CommSq g h' h k)
    (unitsPullback : Sheaf.H.{u} (Sheaf.unitsAddSheaf X.sheaf) 1 →+
      Sheaf.H.{u} (Sheaf.unitsAddSheaf X'.sheaf) 1)
    (logarithmicPullback : H h 1 1 →+ H h' 1 1)
    (dlog_naturality : logarithmicPullback.comp (Sheaf.H.map (dlog h) 1) =
      (Sheaf.H.map (dlog h') 1).comp unitsPullback)
    (picard_naturality : unitsPullback.comp
        (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf) =
      (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X'.sheaf).comp
        (Scheme.Hom.picardPullback g)) : ChernPullback sq where
  unitsPullback := unitsPullback
  logarithmicPullback := logarithmicPullback
  dlog_naturality := dlog_naturality
  picard_naturality := picard_naturality

/-- The pullback comparison built by `ofMaps` retains the supplied logarithmic map. -/
theorem ofMaps_logarithmicPullback (sq : CommSq g h' h k)
    (unitsPullback : Sheaf.H.{u} (Sheaf.unitsAddSheaf X.sheaf) 1 →+
      Sheaf.H.{u} (Sheaf.unitsAddSheaf X'.sheaf) 1)
    (logarithmicPullback : H h 1 1 →+ H h' 1 1)
    (dlog_naturality : logarithmicPullback.comp (Sheaf.H.map (dlog h) 1) =
      (Sheaf.H.map (dlog h') 1).comp unitsPullback)
    (picard_naturality : unitsPullback.comp
        (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X.sheaf) =
      (SheafOfModules.RingedSite.PicardGroup.cohomologyClass X'.sheaf).comp
        (Scheme.Hom.picardPullback g)) :
    (ofMaps sq unitsPullback logarithmicPullback dlog_naturality
      picard_naturality).logarithmicPullback = logarithmicPullback := sorry

end ChernPullback

/-- Pullback naturality of the logarithmic first Chern homomorphism for the canonical maps
owned by a commutative-square comparison. -/
theorem firstChernHom_naturality (sq : CommSq g h' h k) (P : ChernPullback sq) :
    P.logarithmicPullback.comp (firstChernHom h) =
      (firstChernHom h').comp (Scheme.Hom.picardPullback g) := sorry

/-- Canonical pullback carries the logarithmic first Chern class of an invertible module to
the class of its module pullback. -/
theorem firstChernClass_naturality (sq : CommSq g h' h k) (P : ChernPullback sq)
    (L : X.Modules) [Scheme.Modules.Invertible L] :
    P.logarithmicPullback (firstChernClass h L) =
      firstChernClass h' ((Scheme.Modules.pullback g).obj L) := sorry

end AlgebraicGeometry.Scheme.DeRham.LogarithmicForms
