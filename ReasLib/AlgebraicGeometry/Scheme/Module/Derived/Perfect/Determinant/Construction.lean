/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant.AffineRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace ActualGlobalDeterminant

open ActualAffineRestriction

variable (X : Scheme.{u}) (K : Perfect X)

theorem restriction_id (U : X.affineOpens) (s : line X K U) :
    (lineRestriction X K (U := U) (V := U) le_rfl).hom s = s := by sorry

theorem restriction_comp {U V W : X.affineOpens} (hVU : V.1 ≤ U.1) (hWV : W.1 ≤ V.1)
    (s : line X K U) :
    (lineRestriction X K hWV).hom ((lineRestriction X K hVU).hom s) =
      (lineRestriction X K (hWV.trans hVU)).hom s := by sorry

/-- Local values carry the scalar action from the ambient open through the
actual restriction of the structure sheaf. -/
def localModule (W : X.Opens) (U : X.affineOpens) (h : U.1 ≤ W) : ModuleCat Γ(X, W) :=
  (ModuleCat.restrictScalars (ringMap X h)).obj (line X K U)

def familyModule (W : X.Opens) : ModuleCat Γ(X, W) :=
  ModuleCat.of Γ(X, W)
    (∀ U : {U : X.affineOpens // U.1 ≤ W}, localModule X K W U.val U.property)

/-- Full compatible families on ALL affine opens contained in W. There is no
optional support/index choice, including at the empty open. -/
def compatible (W : X.Opens) : Submodule Γ(X, W) (familyModule X K W) where
  carrier := {s | ∀ (U V : X.affineOpens) (hVU : V.1 ≤ U.1) (hUW : U.1 ≤ W),
    (lineRestriction X K hVU).hom (s ⟨U, hUW⟩) = s ⟨V, hVU.trans hUW⟩}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

def sectionsModule (W : X.Opens) : ModuleCat Γ(X, W) :=
  ModuleCat.of Γ(X, W) (compatible X K W)

/-- Restriction of a compatible family merely restricts its affine index set. -/
def restrictionMap {W Z : X.Opens} (h : Z ≤ W) :
    sectionsModule X K W ⟶ (ModuleCat.restrictScalars (ringMap X h)).obj (sectionsModule X K Z) :=
  ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (ringMap X h)).obj (sectionsModule X K Z))
    { toFun := fun s ↦ ⟨fun U ↦ s.val ⟨U.val, U.property.trans h⟩, by sorry⟩
      map_add' := by sorry
      map_smul' := by sorry }

def presheaf : X.PresheafOfModules where
  obj W := sectionsModule X K W.unop
  map h := restrictionMap X K (leOfHom h.unop)
  map_id := by sorry
  map_comp := by sorry

/-- On the affine basis, determinant scalar extension is an isomorphism.
Thus these are the compatible sections of locally free rank-one modules;
the basis sheaf criterion applies to this actual family construction. -/
theorem isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology X)
    (presheaf X K).presheaf := by sorry

/-- Actual global determinant module, as the sheaf of compatible affine
determinant sections. No nonempty-determinant witness is selected. -/
def lineSheaf : X.Modules := ⟨presheaf X K, isSheaf X K⟩

/-- The canonical restriction comparison on an affine U is projection to its
U-component. All other components are forced by compatibility. -/
def affineProjection (U : X.affineOpens) : sectionsModule X K U.1 ⟶ line X K U :=
  ModuleCat.ofHom
    { toFun := fun s ↦ s.val ⟨U, le_rfl⟩
      map_add' := by sorry
      map_smul' := by sorry }

theorem affineProjection_bijective (U : X.affineOpens) :
    Function.Bijective (affineProjection X K U).hom := by sorry

def affineSectionsIso (U : X.affineOpens) : sectionsModule X K U.1 ≅ line X K U :=
  (LinearEquiv.ofBijective (affineProjection X K U).hom
    (affineProjection_bijective X K U)).toModuleIso

def isRankZero : Prop := ∀ U : X.affineOpens,
  CanonicalRingDeterminant.isRankZero Γ(X, U.1) (affineObject X K U)

/-- Canonical elements form a compatible family by the actual scalar-change
comparison and its canonical-element law. -/
def deltaTop (hK : isRankZero X K) : sectionsModule X K ⊤ :=
  ⟨fun U ↦ CanonicalRingDeterminant.canonicalElement Γ(X, U.val.1)
      (affineObject X K U.val) (hK U.val),
    by sorry⟩

def delta (hK : isRankZero X K) : (lineSheaf X K).sections :=
  RingedSpace.sectionFromTop (lineSheaf X K) (deltaTop X K hK)

end ActualGlobalDeterminant
