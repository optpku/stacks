/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BivariantClass
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.Good
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange

/-! # Proper pushforward of algebraic-space bivariant classes -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BivariantClass

variable {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (pZ : Z ⟶ B) [QuasiSeparated pZ] [LocallyOfFiniteType pZ]
variable (f : X ⟶ Y) (g : Y ⟶ Z)
variable [QuasiSeparated (g ≫ pZ)] [LocallyOfFiniteType (g ≫ pZ)]
variable [QuasiSeparated ((f ≫ g) ≫ pZ)] [LocallyOfFiniteType ((f ≫ g) ≫ pZ)]
variable [Proper f]

/-- The cap maps of a pushed-forward class are obtained by proper Chow
pushforward after applying the original cap map to the pasted square. -/
def properPushforwardCapFamily {p : ℤ}
    (c : BivariantClass δ pZ (f ≫ g) p) : CapFamily δ pZ g p :=
  fun {Y' Z'} (i : Y' ⟶ Y) (g' : Y' ⟶ Z') (h : Z' ⟶ Z)
      [QuasiSeparated (h ≫ pZ)] [LocallyOfFiniteType (h ≫ pZ)]
      [QuasiSeparated (i ≫ g ≫ pZ)] [LocallyOfFiniteType (i ≫ g ≫ pZ)]
      (square : IsPullback i g' g h) (k : ℤ) ↦
    (ChowGroup.properPushforward (pullback.fst f i ≫ (f ≫ g) ≫ pZ)
        (i ≫ g ≫ pZ) δ (pullback.snd f i)
        (by
          simpa only [Category.assoc] using
            congrArg (fun q => q ≫ g ≫ pZ)
              (pullback.condition (f := f) (g := i)).symm)
        (k - p)).comp
      (c.cap (pullback.fst f i) (pullback.snd f i ≫ g') h
        ((IsPullback.of_hasPullback f i).paste_vert square) k)

/-- Evaluation of the cap family is proper Chow pushforward after the
original cap map on the pasted square. -/
theorem properPushforwardCapFamily_apply {Y' Z' : AlgebraicSpace S}
    {p : ℤ} (c : BivariantClass δ pZ (f ≫ g) p)
    (i : Y' ⟶ Y) (g' : Y' ⟶ Z') (h : Z' ⟶ Z)
    [QuasiSeparated (h ≫ pZ)] [LocallyOfFiniteType (h ≫ pZ)]
    [QuasiSeparated (i ≫ g ≫ pZ)] [LocallyOfFiniteType (i ≫ g ≫ pZ)]
    (square : IsPullback i g' g h) (k : ℤ) :
    properPushforwardCapFamily δ pZ f g c i g' h square k =
      (ChowGroup.properPushforward (pullback.fst f i ≫ (f ≫ g) ≫ pZ)
          (i ≫ g ≫ pZ) δ (pullback.snd f i)
          (by
            simpa only [Category.assoc] using
              congrArg (fun q => q ≫ g ≫ pZ)
                (pullback.condition (f := f) (g := i)).symm)
          (k - p)).comp
        (c.cap (pullback.fst f i) (pullback.snd f i ≫ g') h
          ((IsPullback.of_hasPullback f i).paste_vert square) k) := by
  rfl

/-- The proper-pushforward cap family is compatible with proper pushforward. -/
theorem properPushforwardCapFamily_map_proper {p : ℤ}
    (c : BivariantClass δ pZ (f ≫ g) p) :
    CompatibleWithProperPushforward δ pZ g
      (properPushforwardCapFamily δ pZ f g c) := sorry

/-- The proper-pushforward cap family is compatible with flat pullback. -/
theorem properPushforwardCapFamily_pullback_flat {p : ℤ}
    (c : BivariantClass δ pZ (f ≫ g) p) :
    CompatibleWithFlatPullback δ pZ g
      (properPushforwardCapFamily δ pZ f g c) := sorry

/-- The proper-pushforward cap family is compatible with Cartier Gysin. -/
theorem properPushforwardCapFamily_gysin_cartier {p : ℤ}
    (c : BivariantClass δ pZ (f ≫ g) p) :
    CompatibleWithCartierGysin δ pZ g
      (properPushforwardCapFamily δ pZ f g c) := sorry

/-- Push a bivariant class forward along the first morphism of a composable
pair when that morphism is proper. -/
def properPushforward (p : ℤ)
    (c : BivariantClass δ pZ (f ≫ g) p) : BivariantClass δ pZ g p :=
  ofCap δ pZ g (properPushforwardCapFamily δ pZ f g c)
    (properPushforwardCapFamily_map_proper δ pZ f g c)
    (properPushforwardCapFamily_pullback_flat δ pZ f g c)
    (properPushforwardCapFamily_gysin_cartier δ pZ f g c)

/-- The cap map of a proper pushforward is the original cap map followed by
proper Chow pushforward on each cartesian test square. -/
theorem properPushforward_cap (p : ℤ) (c : BivariantClass δ pZ (f ≫ g) p)
    {Y' Z' : AlgebraicSpace S}
    (i : Y' ⟶ Y) (g' : Y' ⟶ Z') (h : Z' ⟶ Z)
    [QuasiSeparated (h ≫ pZ)] [LocallyOfFiniteType (h ≫ pZ)]
    [QuasiSeparated (i ≫ g ≫ pZ)] [LocallyOfFiniteType (i ≫ g ≫ pZ)]
    (square : IsPullback i g' g h) (k : ℤ) :
    (properPushforward δ pZ f g p c).cap i g' h square k =
      (ChowGroup.properPushforward (pullback.fst f i ≫ (f ≫ g) ≫ pZ)
          (i ≫ g ≫ pZ) δ (pullback.snd f i)
          (by
            simpa only [Category.assoc] using
              congrArg (fun q => q ≫ g ≫ pZ)
                (pullback.condition (f := f) (g := i)).symm)
          (k - p)).comp
        (c.cap (pullback.fst f i) (pullback.snd f i ≫ g') h
          ((IsPullback.of_hasPullback f i).paste_vert square) k) := by
  rfl

/-- On the chosen fibre product over `Z`, the cap of a proper pushforward is
the original cap followed by proper Chow pushforward. -/
theorem properPushforward_cap_pullback (p : ℤ)
    (c : BivariantClass δ pZ (f ≫ g) p) {Z' : AlgebraicSpace S} (h : Z' ⟶ Z)
    [QuasiSeparated (h ≫ pZ)] [LocallyOfFiniteType (h ≫ pZ)]
    [QuasiSeparated (pullback.fst g h ≫ g ≫ pZ)]
    [LocallyOfFiniteType (pullback.fst g h ≫ g ≫ pZ)] (k : ℤ) :
    (properPushforward δ pZ f g p c).cap (pullback.fst g h) (pullback.snd g h) h
        (IsPullback.of_hasPullback g h) k =
      (ChowGroup.properPushforward
          (pullback.fst f (pullback.fst g h) ≫ (f ≫ g) ≫ pZ)
          (pullback.fst g h ≫ g ≫ pZ) δ
          (pullback.snd f (pullback.fst g h))
          (by
            simpa only [Category.assoc] using
              congrArg (fun q => q ≫ g ≫ pZ)
                (pullback.condition (f := f) (g := pullback.fst g h)).symm)
          (k - p)).comp
        (c.cap (pullback.fst f (pullback.fst g h))
          (pullback.snd f (pullback.fst g h) ≫ pullback.snd g h) h
          ((IsPullback.of_hasPullback f (pullback.fst g h)).paste_vert
            (IsPullback.of_hasPullback g h)) k) := by
  rfl

end AlgebraicGeometry.AlgebraicSpace.BivariantClass
