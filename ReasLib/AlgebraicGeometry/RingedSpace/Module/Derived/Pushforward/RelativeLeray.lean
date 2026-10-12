/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.RelativeLeray
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative Leray spectral sequences on ringed spaces

The data owners in this leaf are definitional specializations of
`RingedSite.Hom.RelativeLeray` to opens ringed sites.  The companion propositions compare their
generic targets with the ordinary ringed-space higher-direct-image notation; no second realization
or map structure is introduced.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleRelativeLeray

variable {X Y Z : RingedSpace.{u}}

/-- The canonical ordinary relative Leray realization on opens ringed sites. -/
@[stacks 01F6 "ringed-space relative Leray realization"]
abbrev Realization (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules) :=
  RingedSite.Hom.RelativeLeray.{u} (opensRingedSiteHom f) (opensRingedSiteHom g) F

/-- The canonical ordinary relative Leray page-two target. -/
@[stacks 01F6 "ringed-space relative Leray page two"]
abbrev pageTwo (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules)
    (p q : ℕ) : Z.Modules :=
  RingedSite.Hom.RelativeLeray.pageTwo.{u}
    (opensRingedSiteHom f) (opensRingedSiteHom g) F p q

/-- The textbook ordinary page-two target `R^p g_* (R^q f_* F)`. -/
@[stacks 01F6 "higher-direct-image relative Leray page two"]
abbrev higherDirectImagePageTwo (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules)
    (p q : ℕ) : Z.Modules :=
  higherDirectImageModule g (higherDirectImageModule f F q) p

/-- The canonical ordinary relative Leray abutment. -/
@[stacks 01F6 "ringed-space relative Leray abutment"]
abbrev abutment (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules)
    (n : ℕ) : Z.Modules :=
  RingedSite.Hom.RelativeLeray.abutment.{u}
    (opensRingedSiteHom f) (opensRingedSiteHom g) F n

/-- The textbook ordinary abutment `R^n (g ∘ f)_* F`. -/
@[stacks 01F6 "higher-direct-image relative Leray abutment"]
abbrev higherDirectImageAbutment (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules)
    (n : ℕ) : Z.Modules :=
  higherDirectImageModule (f ≫ g) F n

/-- The generic ordinary page-two target is isomorphic to its higher-direct-image presentation. -/
@[stacks 01F6 "relative Leray page-two comparison"]
theorem pageTwo_isIsomorphic_higherDirectImage (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : X.Modules) (p q : ℕ) :
    IsIsomorphic (pageTwo f g F p q) (higherDirectImagePageTwo f g F p q) := sorry

/-- The generic ordinary abutment is isomorphic to the higher direct image along the composite. -/
@[stacks 01F6 "relative Leray abutment comparison"]
theorem abutment_isIsomorphic_higherDirectImage (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : X.Modules) (n : ℕ) :
    IsIsomorphic (abutment f g F n) (higherDirectImageAbutment f g F n) := sorry

/-- The functorial relative Leray owner specialized to opens ringed sites. -/
@[stacks 01F6 "functorial ringed-space relative Leray spectral sequence"]
abbrev Functorial (f : X ⟶ Y) (g : Y ⟶ Z) :=
  RingedSite.Hom.RelativeLeray.Functorial.{u}
    (opensRingedSiteHom f) (opensRingedSiteHom g)

/-- Relative Leray realizations can be chosen functorially in the input module. -/
@[stacks 01F6 "functorial relative Leray existence"]
theorem functorial (f : X ⟶ Y) (g : Y ⟶ Z) :
    Nonempty (Functorial f g) := sorry

/-- Every module sheaf admits the canonical ordinary relative Leray realization. -/
@[stacks 01F6 "existence of the relative Leray spectral sequence"]
theorem nonempty (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules) :
    Nonempty (Realization f g F) := sorry

/-- A module morphism admits compatible ordinary realizations and a realization map. -/
@[stacks 01F6 "map of relative Leray spectral sequences"]
theorem existsMap (f : X ⟶ Y) (g : Y ⟶ Z) {F G : X.Modules} (φ : F ⟶ G) :
    ∃ (S : Realization f g F) (T : Realization f g G),
      Nonempty (RingedSite.Hom.RelativeLeray.Map.{u} φ S T) := sorry

/-- The canonical bounded-below relative Leray realization on opens ringed sites. -/
@[stacks 01F6 "bounded-below ringed-space relative Leray realization"]
abbrev BoundedBelow (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory.Plus X.Modules) :=
  RingedSite.Hom.RelativeLeray.BoundedBelow.{u, u, u, u, u, u, u, u}
    (opensRingedSiteHom f) (opensRingedSiteHom g) K

namespace BoundedBelow

/-- The canonical bounded-below relative Leray page-two target. -/
@[stacks 01F6 "bounded-below ringed-space relative Leray page two"]
abbrev pageTwo (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory.Plus X.Modules) (p : ℕ) (q : ℤ) : Z.Modules :=
  RingedSite.Hom.RelativeLeray.BoundedBelow.pageTwo.{u, u, u, u, u, u, u, u}
    (opensRingedSiteHom f) (opensRingedSiteHom g) K p q

/-- The textbook bounded-below page-two target `R^p g_* (H^q(Rf_* K))`. -/
@[stacks 01F6 "bounded-below higher-direct-image page two"]
abbrev higherDirectImagePageTwo (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory.Plus X.Modules) (p : ℕ) (q : ℤ) : Z.Modules :=
  higherDirectImageModule g (moduleDerivedPushforwardPlus.cohomology f K q) p

/-- The canonical bounded-below relative Leray abutment. -/
@[stacks 01F6 "bounded-below ringed-space relative Leray abutment"]
abbrev abutment (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory.Plus X.Modules) (n : ℤ) : Z.Modules :=
  RingedSite.Hom.RelativeLeray.BoundedBelow.abutment.{u, u, u, u, u, u, u, u}
    (opensRingedSiteHom f) (opensRingedSiteHom g) K n

/-- The textbook bounded-below abutment `H^n(R(g ∘ f)_* K)`. -/
@[stacks 01F6 "bounded-below derived-pushforward abutment"]
abbrev derivedPushforwardAbutment (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory.Plus X.Modules) (n : ℤ) : Z.Modules :=
  moduleDerivedPushforwardPlus.cohomology (f ≫ g) K n

/-- The generic bounded-below page-two target has the textbook higher-direct-image presentation. -/
@[stacks 01F6 "bounded-below relative Leray page-two comparison"]
theorem pageTwo_isIsomorphic_higherDirectImage (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory.Plus X.Modules) (p : ℕ) (q : ℤ) :
    IsIsomorphic (pageTwo f g K p q) (higherDirectImagePageTwo f g K p q) := sorry

/-- The generic bounded-below abutment has the composite derived-pushforward presentation. -/
@[stacks 01F6 "bounded-below relative Leray abutment comparison"]
theorem abutment_isIsomorphic_derivedPushforward (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategory.Plus X.Modules) (n : ℤ) :
    IsIsomorphic (abutment f g K n) (derivedPushforwardAbutment f g K n) := sorry

/-- The functorial bounded-below relative Leray owner specialized to opens ringed sites. -/
@[stacks 01F6 "functorial bounded-below ringed-space relative Leray spectral sequence"]
abbrev Functorial (f : X ⟶ Y) (g : Y ⟶ Z) :=
  RingedSite.Hom.RelativeLeray.BoundedBelow.Functorial.{u, u, u, u, u, u, u, u}
    (opensRingedSiteHom f) (opensRingedSiteHom g)

/-- Bounded-below relative Leray realizations can be chosen functorially in the derived module. -/
@[stacks 01F6 "functorial bounded-below relative Leray existence"]
theorem functorial (f : X ⟶ Y) (g : Y ⟶ Z) :
    Nonempty (Functorial f g) := sorry

/-- Every bounded-below derived module admits the canonical relative Leray realization. -/
@[stacks 01F6 "bounded-below relative Leray existence"]
theorem nonempty (f : X ⟶ Y) (g : Y ⟶ Z) (K : DerivedCategory.Plus X.Modules) :
    Nonempty (BoundedBelow f g K) := sorry

/-- A derived morphism admits compatible bounded-below realizations and a realization map. -/
@[stacks 01F6 "bounded-below relative Leray map"]
theorem existsMap (f : X ⟶ Y) (g : Y ⟶ Z)
    {K L : DerivedCategory.Plus X.Modules} (φ : K ⟶ L) :
    ∃ (S : BoundedBelow f g K) (T : BoundedBelow f g L),
      Nonempty (RingedSite.Hom.RelativeLeray.BoundedBelow.Map.{u, u, u, u, u, u, u, u}
        φ S T) := sorry

end BoundedBelow

end AlgebraicGeometry.RingedSpace.ModuleRelativeLeray
