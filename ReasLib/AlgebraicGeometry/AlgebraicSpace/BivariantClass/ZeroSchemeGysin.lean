/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BivariantClass
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.ProperPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback

/-!
# Zero-scheme Gysin as a bivariant class

A section of an invertible module on a good algebraic space over a base with
a dimension function determines a degree-one bivariant class. Its cap maps
are refined Gysin along the pulled-back section, transported to each displayed
cartesian base change of its zero scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.BivariantClass

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
variable (L : X.Modules) [isInvertibleObject L] (s : L.sections)

/-- The canonical comparison from the zero scheme of the pulled-back section
to the source of a displayed cartesian square for `zeroSchemeι L s`. -/
noncomputable def gysinBaseChangeIso {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [isInvertibleObject ((Modules.pullback g).obj L)]
    (square : IsPullback j i' (zeroSchemeι L s) g) :
    (zeroScheme ((Modules.pullback g).obj L)
        (Modules.sectionsPullback g L s)).X ≅ D' :=
  (zeroSchemePullbackSquare g L s).isoIsPullback _ _ square.flip

/-- The Gysin base-change isomorphism respects structure morphisms over `B`. -/
theorem gysinBaseChangeIso_hom_comp_structure {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [isInvertibleObject ((Modules.pullback g).obj L)]
    (square : IsPullback j i' (zeroSchemeι L s) g) :
    (gysinBaseChangeIso L s j i' g square).hom ≫
        (j ≫ zeroSchemeι L s ≫ pX) =
      zeroSchemeι ((Modules.pullback g).obj L)
          (Modules.sectionsPullback g L s) ≫ g ≫ pX :=
  sorry

/-- Chow-level refined Gysin along a cartesian square whose pulled-back
module is already known to be invertible. -/
noncomputable def chowGysin_isPullback.ofInvertible {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
    [QuasiSeparated (j ≫ zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType (j ≫ zeroSchemeι L s ≫ pX)]
    [isInvertibleObject ((Modules.pullback g).obj L)]
    (square : IsPullback j i' (zeroSchemeι L s) g) (k : ℤ) :
    Hom.chowGroup (g ≫ pX) δ k →+
      Hom.chowGroup (j ≫ zeroSchemeι L s ≫ pX) δ (k - 1) :=
  (ChowGroup.properPushforward
      (zeroSchemeι ((Modules.pullback g).obj L)
        (Modules.sectionsPullback g L s) ≫ g ≫ pX)
      (j ≫ zeroSchemeι L s ≫ pX) δ
      (gysinBaseChangeIso L s j i' g square).hom
      (gysinBaseChangeIso_hom_comp_structure pX L s j i' g square) (k - 1)).comp
    ((ChowGroup.RefinedGysin.gysin (g ≫ pX) δ ((Modules.pullback g).obj L)
        (Modules.sectionsPullback g L s) (k - 1)).comp
      (castChowGroup δ (g ≫ pX) (sub_add_cancel k 1).symm))

/-- Unfolding of `chowGysin_isPullback.ofInvertible` as proper pushforward of
Chow-level Gysin, after reindexing `k - 1 + 1 = k`. -/
theorem chowGysin_isPullback.ofInvertible_apply {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
    [QuasiSeparated (j ≫ zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType (j ≫ zeroSchemeι L s ≫ pX)]
    [isInvertibleObject ((Modules.pullback g).obj L)]
    (square : IsPullback j i' (zeroSchemeι L s) g) (k : ℤ) :
    chowGysin_isPullback.ofInvertible δ pX L s j i' g square k =
      (ChowGroup.properPushforward
          (zeroSchemeι ((Modules.pullback g).obj L)
            (Modules.sectionsPullback g L s) ≫ g ≫ pX)
          (j ≫ zeroSchemeι L s ≫ pX) δ
          (gysinBaseChangeIso L s j i' g square).hom
          (gysinBaseChangeIso_hom_comp_structure pX L s j i' g square)
          (k - 1)).comp
        ((ChowGroup.RefinedGysin.gysin (g ≫ pX) δ ((Modules.pullback g).obj L)
            (Modules.sectionsPullback g L s) (k - 1)).comp
          (castChowGroup δ (g ≫ pX)
            (sub_add_cancel k 1).symm)) :=
  sorry

/-- Chow-level refined Gysin along the left vertical of a cartesian square
for `zeroSchemeι L s`, transported along `gysinBaseChangeIso`. Invertibility
of the pulled-back module is supplied by `Modules.isInvertibleObject_pullback`. -/
noncomputable def chowGysin_isPullback {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
    [QuasiSeparated (j ≫ zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType (j ≫ zeroSchemeι L s ≫ pX)]
    (square : IsPullback j i' (zeroSchemeι L s) g) (k : ℤ) :
    Hom.chowGroup (g ≫ pX) δ k →+
      Hom.chowGroup (j ≫ zeroSchemeι L s ≫ pX) δ (k - 1) :=
  chowGysin_isPullback.ofInvertible δ pX L s j i' g square k

/-- Cap family of transported Chow-level Gysin maps, as a degree-`1`
operation. -/
noncomputable def gysinCapFamily : CapFamily δ pX (zeroSchemeι L s) 1 :=
  fun {D' X'} (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
      [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
      [QuasiSeparated (j ≫ zeroSchemeι L s ≫ pX)]
      [LocallyOfFiniteType (j ≫ zeroSchemeι L s ≫ pX)]
      (square : IsPullback j i' (zeroSchemeι L s) g) (k : ℤ) ↦
    chowGysin_isPullback δ pX L s j i' g square k

/-- Unfolding of `gysinCapFamily` as cartesian refined Gysin. -/
theorem gysinCapFamily_apply {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
    [QuasiSeparated (j ≫ zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType (j ≫ zeroSchemeι L s ≫ pX)]
    (square : IsPullback j i' (zeroSchemeι L s) g) (k : ℤ) :
    gysinCapFamily δ pX L s j i' g square k =
      chowGysin_isPullback δ pX L s j i' g square k :=
  sorry

/-- The Gysin cap family is compatible with proper pushforward. -/
theorem gysinCapFamily_map_proper :
    CompatibleWithProperPushforward δ pX (zeroSchemeι L s)
      (gysinCapFamily δ pX L s) :=
  sorry

/-- The Gysin cap family is compatible with flat pullback. -/
theorem gysinCapFamily_pullback_flat :
    CompatibleWithFlatPullback δ pX (zeroSchemeι L s)
      (gysinCapFamily δ pX L s) :=
  sorry

/-- The Gysin cap family is compatible with Cartier Gysin. -/
theorem gysinCapFamily_gysin_cartier :
    CompatibleWithCartierGysin δ pX (zeroSchemeι L s)
      (gysinCapFamily δ pX L s) :=
  sorry

/-- The refined Gysin maps of a section of an invertible module form a
bivariant class of degree one for its zero-scheme immersion. -/
noncomputable def gysin : BivariantClass δ pX (zeroSchemeι L s) 1 :=
  ofCap δ pX (zeroSchemeι L s) (gysinCapFamily δ pX L s)
    (gysinCapFamily_map_proper δ pX L s)
    (gysinCapFamily_pullback_flat δ pX L s)
    (gysinCapFamily_gysin_cartier δ pX L s)

/-- The cap maps of `gysin` are the transported Chow-level Gysin maps. -/
theorem gysin_cap {D' X' : AlgebraicSpace S}
    (j : D' ⟶ (zeroScheme L s).X) (i' : D' ⟶ X') (g : X' ⟶ X)
    [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
    [QuasiSeparated (j ≫ zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType (j ≫ zeroSchemeι L s ≫ pX)]
    (square : IsPullback j i' (zeroSchemeι L s) g) (k : ℤ) :
    (gysin δ pX L s).cap j i' g square k =
      gysinCapFamily δ pX L s j i' g square k :=
  sorry

/-- On the chosen fibre product `D' = D ×_X X'`, the cap of `gysin` is the
transported Chow-level Gysin along `pullback.snd (zeroSchemeι L s) g`. -/
theorem gysin_cap_pullback {X' : AlgebraicSpace S} (g : X' ⟶ X)
    [QuasiSeparated (g ≫ pX)] [LocallyOfFiniteType (g ≫ pX)]
    [QuasiSeparated (pullback.fst (zeroSchemeι L s) g ≫ zeroSchemeι L s ≫ pX)]
    [LocallyOfFiniteType
      (pullback.fst (zeroSchemeι L s) g ≫ zeroSchemeι L s ≫ pX)] (k : ℤ) :
    (gysin δ pX L s).cap
        (pullback.fst (zeroSchemeι L s) g)
        (pullback.snd (zeroSchemeι L s) g) g
        (IsPullback.of_hasPullback (zeroSchemeι L s) g) k =
      chowGysin_isPullback δ pX L s
        (pullback.fst (zeroSchemeι L s) g)
        (pullback.snd (zeroSchemeι L s) g) g
        (IsPullback.of_hasPullback (zeroSchemeι L s) g) k :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.BivariantClass
