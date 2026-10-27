/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.BaseChange

/-! # Flat pullback and refined Gysin homomorphisms -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin

variable {S : Scheme.{u}} {B X X' : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
  (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
  (pX' : X' ⟶ B) [QuasiSeparated pX'] [LocallyOfFiniteType pX']
  (δ : Points B → ℤ) [IsDimensionFunction δ]
  (f : X' ⟶ X) (r : ℕ) [Flat f] [RelativeDimension f r]
  (hf : f ≫ pX = pX') (L : X.Modules) [isInvertibleObject L] (s : L.sections)
  [isInvertibleObject ((Modules.pullback f).obj L)]

include pX pX' hf in
/-- The map on zero schemes in a flat square of good algebraic spaces has
the same relative dimension as the ambient morphism. -/
private theorem goodBaseChange_relativeDimension :
    RelativeDimension (zeroSchemePullbackMap f L s) r := sorry

/-- Chow pullback along the actual map between zero schemes of a section and
its pullback along a flat morphism of good algebraic spaces. -/
def baseChangeFlatPullback (k : ℤ) :
    Hom.chowGroup (zeroSchemeι L s ≫ pX) δ k →+
      Hom.chowGroup
        (zeroSchemeι ((Modules.pullback f).obj L)
          (Modules.sectionsPullback f L s) ≫ pX') δ (k + (r : ℤ)) :=
  @ChowGroup.flatPullback S B
    (zeroScheme ((Modules.pullback f).obj L) (Modules.sectionsPullback f L s)).X
    (zeroScheme L s).X inferInstance inferInstance
    (zeroSchemeι L s ≫ pX) inferInstance inferInstance
    (zeroSchemeι ((Modules.pullback f).obj L)
      (Modules.sectionsPullback f L s) ≫ pX') inferInstance inferInstance δ inferInstance
    (zeroSchemePullbackMap f L s) r
    (Flat.of_isPullback (zeroSchemePullbackSquare f L s) inferInstance)
    (by exact goodBaseChange_relativeDimension pX pX' f r hf L s)
    (by rw [← Category.assoc, zeroSchemePullbackMap_comp, Category.assoc, hf]) k

end AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Refined Gysin commutes with flat pullback of cycles and Chow classes,
with the relative-dimension degree shift, in the zero-scheme cartesian square. -/
theorem gysin_flatPullback_eq_flatPullback_gysin {S : Scheme.{u}}
    {B X X' : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pX' : X' ⟶ B) [QuasiSeparated pX'] [LocallyOfFiniteType pX']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X' ⟶ X) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pX = pX') (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) [isInvertibleObject ((Modules.pullback f).obj L)]
    (k : ℤ) (α : cycleGroup pX δ (k + 1)) :
    gysin pX' δ (k + (r : ℤ)) ((Modules.pullback f).obj L)
        (Modules.sectionsPullback f L s)
        (add_right_comm k 1 (r : ℤ) ▸ flatPullbackHom pX pX' δ f r hf (k + 1) α) =
      ChowGroup.RefinedGysin.baseChangeFlatPullback pX pX' δ f r hf L s k
        (gysin pX δ k L s α) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
