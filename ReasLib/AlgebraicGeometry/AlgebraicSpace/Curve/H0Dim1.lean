/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Target
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Germ.Morphism.CohenMacaulay

/-!
# Curves with universally trivial structure-sheaf pushforward

Universally trivial structure-sheaf pushforward together with fibres of dimension
one is represented by an open of the base of each family of curves. For a proper
scheme over a field, this condition is characterized by its canonical map on
global sections and its dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The object property of families of curves with universally trivial
`𝒪_S ⟶ f_* 𝒪_X` and fibres of dimension `1`. -/
def h0Dim1 (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦
    (∀ {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
        IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g))) ∧
      ∀ y : Points (ofOver (base P)), fiberDimension (hom P) y = 1

/-- Membership in `h0Dim1` means the unit `𝒪_S ⟶ f_* 𝒪_X` is an isomorphism
after every base change, including the identity, and every fibre has
dimension `1`. -/
theorem h0Dim1_iff {S : Scheme.{u}} (P : Obj S) :
    h0Dim1 S P ↔
      (∀ {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g))) ∧
        ∀ y : Points (ofOver (base P)), fiberDimension (hom P) y = 1 := Iff.rfl

/-- The `h0Dim1` property of families of curves is closed under isomorphisms. -/
instance instIsClosedUnderIsomorphisms_h0Dim1 (S : Scheme.{u}) :
    (h0Dim1 S).IsClosedUnderIsomorphisms :=
  sorry

/-- For every family of curves, an open of its base represents the property of
universally trivial structure-sheaf pushforward and fibres of dimension one
under every cartesian morphism of families. -/
theorem exists_h0Dim1_open {S : Scheme.{u}} (P : Obj S) :
    ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
      h0Dim1 S Q ↔ Set.range (baseMap φ).left ⊆ U :=
  sorry

/-- A proper scheme of dimension at most one over a field defines a curve family
with universally trivial structure-sheaf pushforward and fibres of dimension one
precisely when its canonical map on global sections is bijective and its
dimension is one. -/
theorem classifying_factorsThrough_h0Dim1_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    h0Dim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ∧
        topologicalKrullDim X.left = 1 :=
  sorry

/-- A family of curves with universally trivial structure-sheaf pushforward and
one-dimensional fibres is flat at every point, has Cohen–Macaulay fibre stalks
on étale scheme squares through every point, and has relative dimension one. -/
theorem h0Dim1_le_cohenMacaulayDim1 (S : Scheme.{u}) :
    h0Dim1 S ≤ fun P ↦
      (∀ x : Points (space P),
          FlatAt (hom P) x ∧
            existsEtaleSquareAt Scheme.Germ.MorphismProperty.fiberStalkCohenMacaulay
              (hom P) x) ∧
        RelativeDimension (hom P) 1 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
