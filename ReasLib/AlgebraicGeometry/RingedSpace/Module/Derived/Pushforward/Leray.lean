/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.Leray
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Leray spectral sequences for module sheaves on ringed spaces

The ringed-space API is a specialization of `RingedSite.Hom.Leray` to the opens ringed sites; it
does not own a second realization structure.  Companion propositions identify the generic page
and abutment targets with the customary ringed-space cohomology expressions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleLeray

variable {X Y : RingedSpace.{u}}

/-- The canonical Leray realization on the opens ringed sites. -/
@[stacks 01F2 "ringed-space Leray realization"]
abbrev Realization (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules) :=
  RingedSite.Hom.Leray.{u} (opensRingedSiteHom f) K

/-- The canonical `(p, q)` page-two target of the opens-site Leray realization. -/
@[stacks 01F2 "ringed-space Leray page two"]
abbrev pageTwo (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules)
    (p : ℕ) (q : ℤ) : AddCommGrpCat.{u} :=
  RingedSite.Hom.Leray.pageTwo.{u} (opensRingedSiteHom f) K p q

/-- The textbook page-two target `H^p(Y, R^q f_* K)`. -/
@[stacks 01F2 "cohomological Leray page two"]
abbrev cohomologyPageTwo (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules)
    (p : ℕ) (q : ℤ) : AddCommGrpCat.{u} :=
  (forget₂ (ModuleCat (sectionsRingOnOpen Y (⊤ : Opens Y.carrier))) AddCommGrpCat.{u}).obj
    (moduleCohomologyAtOpen (⊤ : Opens Y.carrier)
      (moduleDerivedPushforwardPlus.cohomology f K q) p)

/-- The canonical degree-`n` abutment target of the opens-site Leray realization. -/
@[stacks 01F2 "ringed-space Leray abutment"]
abbrev abutment (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules)
    (n : ℤ) : AddCommGrpCat.{u} :=
  RingedSite.Hom.Leray.abutment.{u} (opensRingedSiteHom f) K n

/-- The textbook Leray abutment `H^n(X, K)`. -/
@[stacks 01F2 "Leray hypercohomology abutment"]
abbrev hypercohomologyAbutment (K : DerivedCategory.Plus X.Modules)
    (n : ℤ) : AddCommGrpCat.{u} :=
  moduleOpenHypercohomology X (⊤ : Opens X.carrier)
    (DerivedCategory.Plus.ι.obj K) n

/-- The canonical page-two target is isomorphic to `H^p(Y, R^q f_* K)`. -/
@[stacks 01F2 "Leray page-two cohomology comparison"]
theorem pageTwo_isIsomorphic_cohomology (f : X ⟶ Y)
    (K : DerivedCategory.Plus X.Modules) (p : ℕ) (q : ℤ) :
    IsIsomorphic (pageTwo f K p q) (cohomologyPageTwo f K p q) := sorry

/-- The canonical Leray abutment is isomorphic to the hypercohomology of the source. -/
@[stacks 01F2 "Leray hypercohomology comparison"]
theorem abutment_isIsomorphic_hypercohomology (f : X ⟶ Y)
    (K : DerivedCategory.Plus X.Modules) (n : ℤ) :
    IsIsomorphic (abutment f K n) (hypercohomologyAbutment K n) := sorry

/-- The functorial Leray owner specialized to the opens ringed sites. -/
@[stacks 01F2 "functorial ringed-space Leray spectral sequence"]
abbrev Functorial (f : X ⟶ Y) :=
  RingedSite.Hom.Leray.Functorial.{u} (opensRingedSiteHom f)

/-- Opens-site Leray realizations can be chosen functorially in the derived module. -/
@[stacks 01F2 "functorial Leray existence"]
theorem functorial (f : X ⟶ Y) : Nonempty (Functorial f) := sorry

/-- Lemma 20.13.4: every bounded-below derived module admits the canonical opens-site Leray
realization. -/
@[stacks 01F2 "existence of the Leray spectral sequence"]
theorem nonempty (f : X ⟶ Y) (K : DerivedCategory.Plus X.Modules) :
    Nonempty (Realization f K) := sorry

/-- A map of derived modules admits compatible opens-site Leray realizations and a realization map.
-/
@[stacks 01F2 "map of Leray spectral sequences"]
theorem existsMap (f : X ⟶ Y) {K L : DerivedCategory.Plus X.Modules}
    (φ : K ⟶ L) :
    ∃ (S : Realization f K) (T : Realization f L),
      Nonempty (RingedSite.Hom.Leray.Map.{u} φ S T) := sorry

end AlgebraicGeometry.RingedSpace.ModuleLeray
