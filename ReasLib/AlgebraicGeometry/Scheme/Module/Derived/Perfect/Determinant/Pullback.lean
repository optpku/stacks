/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Sections

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PerfectDerived.TorNegOneZero

variable {X Y : Scheme.{u}}

variable [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
variable [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]

/-- Derived pullback preserves Tor-amplitude in `[-1, 0]` for perfect derived objects. -/
theorem pullbackMapsTo (f : X ⟶ Y) :
    ((fun K : @RingedSpace.ModuleDerived.Perfect Y.toRingedSpace ↦
        RingedSpace.HasTorAmplitudeIn K.obj (-1) 0) :
      ObjectProperty _) ≤
      ObjectProperty.inverseImage
        ((fun K : @RingedSpace.ModuleDerived.Perfect X.toRingedSpace ↦
          RingedSpace.HasTorAmplitudeIn K.obj (-1) 0) : ObjectProperty _)
        (RingedSpace.modulePullbackPerfect f.toShHom) := sorry

/-- Derived pullback along `f : X ⟶ Y`, restricted to perfect objects of
Tor-amplitude in `[-1, 0]`. -/
noncomputable def pullback (f : X ⟶ Y) : TorNegOneZero Y ⥤ TorNegOneZero X :=
  ObjectProperty.FullSubcategory.restrict
    (RingedSpace.modulePullbackPerfect f.toShHom) (pullbackMapsTo f)

/-- Forgetting the Tor-amplitude condition identifies the bundled pullback with derived
pullback on perfect objects. -/
theorem pullback_obj (f : X ⟶ Y) (K : TorNegOneZero Y) :
    ((pullback f).obj K).obj.obj =
      ((RingedSpace.modulePullbackPerfect f.toShHom).obj K.obj).obj := sorry

namespace Determinant

/-- The functor from perfect objects of Tor-amplitude in `[-1, 0]` to their underlying
determinant-line modules. -/
def lineFunctor {Z : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z.toRingedSpace)]
    (D : Determinant Z) :
    CategoryTheory.Core (TorNegOneZero Z) ⥤ Z.Modules :=
  D.det ⋙ Scheme.Modules.Invertible.inclusion Z

/-- Compatibility data for determinant constructions under one fixed scheme morphism. -/
structure Pullback (f : X ⟶ Y) where
  /-- The determinant construction on the target scheme. -/
  source : Determinant Y
  /-- The determinant construction on the source scheme. -/
  target : Determinant X
  /-- The canonical comparison, natural in the perfect object, between pullback of its
  determinant line and the determinant line of its derived pullback. -/
  lineNatIso :
    lineFunctor source ⋙ Scheme.Modules.pullback f ≅
      (pullback f).core ⋙ lineFunctor target
  /-- Derived pullback preserves the rank-zero locus of the determinant construction. -/
  rankZero : ∀ L : TorNegOneZero Y, source.isRankZero L →
    target.isRankZero ((pullback f).obj L)
  /-- The determinant-line comparison carries the pulled-back canonical section to the
  canonical section of the derived pullback. -/
  canonicalElement : ∀ (L : TorNegOneZero Y) (hL : source.isRankZero L),
    SheafOfModules.sectionsMap (lineNatIso.hom.app ⟨L⟩)
        (RingedSpace.Hom.pullbackSections f.toShHom
          (RingedSpace.sectionFromTop (source.line L) (source.canonicalElement L hL))) =
      RingedSpace.sectionFromTop (target.line ((pullback f).obj L))
        (target.canonicalElement ((pullback f).obj L) (rankZero L hL))

namespace Pullback

/-- Build compatibility data for determinant constructions under a fixed scheme morphism. -/
def of {X Y : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    (f : X ⟶ Y) (source : Determinant Y) (target : Determinant X)
    (lineNatIso : lineFunctor source ⋙ Scheme.Modules.pullback f ≅
      (pullback f).core ⋙ lineFunctor target)
    (rankZero : ∀ L : TorNegOneZero Y, source.isRankZero L →
      target.isRankZero ((pullback f).obj L))
    (canonicalElement : ∀ (L : TorNegOneZero Y) (hL : source.isRankZero L),
      SheafOfModules.sectionsMap (lineNatIso.hom.app ⟨L⟩)
          (RingedSpace.Hom.pullbackSections f.toShHom
            (RingedSpace.sectionFromTop (source.line L) (source.canonicalElement L hL))) =
        RingedSpace.sectionFromTop (target.line ((pullback f).obj L))
          (target.canonicalElement ((pullback f).obj L) (rankZero L hL))) :
    Pullback f :=
  { source := source
    target := target
    lineNatIso := lineNatIso
    rankZero := rankZero
    canonicalElement := canonicalElement }

/-- The component at `K` of the natural determinant-line comparison for pullback. -/
def lineIso {X Y : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    {f : X ⟶ Y} (P : Pullback f) (K : TorNegOneZero Y) :
    (Scheme.Modules.pullback f).obj (P.source.line K) ≅
      P.target.line ((pullback f).obj K) :=
  P.lineNatIso.app ⟨K⟩

/-- Every scheme morphism admits determinant constructions compatible with derived pullback. -/
theorem nonempty {X Y : Scheme.{u}}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    (f : X ⟶ Y) : Nonempty (Pullback f) := sorry

end Pullback
end Determinant

end AlgebraicGeometry.Scheme.PerfectDerived.TorNegOneZero
