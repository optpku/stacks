/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.CurveDegree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Sections and degrees of invertible modules on proper curves

This file records degree and triviality criteria arising from nonzero sections and nonzero
morphisms of invertible modules on proper curves.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module on a proper curve with a nonzero global section has nonnegative
degree. -/
theorem curveDegreeOfInvertible_nonneg_of_nonzero_section
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
    {ℒ : X.left.Modules} [Invertible ℒ] (s : ℒ.sections)
    (hs : ℒ.unitHomEquiv.symm s ≠ 0) :
    0 ≤ curveDegreeOfInvertible X.hom (topologicalKrullDim_eq_one X).le ℒ := sorry

/-- An invertible module on a proper curve with a nonzero global section whose zero scheme is
nonempty has positive degree. -/
theorem curveDegreeOfInvertible_pos_of_nonzero_section_of_nonempty_zeroScheme
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
    {ℒ : X.left.Modules} [Invertible ℒ] (s : ℒ.sections)
    (hs : ℒ.unitHomEquiv.symm s ≠ 0) (hz : Nonempty (Scheme.zeroScheme ℒ s)) :
    0 < curveDegreeOfInvertible X.hom (topologicalKrullDim_eq_one X).le ℒ := sorry

/-- An invertible module on a proper curve is isomorphic to the structure module when it and
its inverse tensor power both have nonzero global sections. -/
theorem isoUnit_of_nonzero_section_of_nonzero_section_inverse
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
    {ℒ : X.left.Modules} [Invertible ℒ]
    (s : ℒ.sections) (hs : ℒ.unitHomEquiv.symm s ≠ 0)
    (t : (tensorPowerInt ℒ (-1)).sections)
    (ht : (tensorPowerInt ℒ (-1)).unitHomEquiv.symm t ≠ 0) :
    Nonempty
      (ℒ ≅ (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)) := sorry

/-- An invertible module on a proper curve with nonpositive degree and a nonzero global section
is isomorphic to the structure module. -/
theorem isoUnit_of_curveDegreeOfInvertible_nonpos_of_nonzero_section
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
    {ℒ : X.left.Modules} [Invertible ℒ]
    (hdeg : curveDegreeOfInvertible X.hom (topologicalKrullDim_eq_one X).le ℒ ≤ 0)
    (s : ℒ.sections) (hs : ℒ.unitHomEquiv.symm s ≠ 0) :
    Nonempty
      (ℒ ≅ (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)) := sorry

/-- A nonzero morphism between invertible modules on a proper curve weakly increases degree. -/
theorem curveDegreeOfInvertible_le_curveDegreeOfInvertible_of_nonzero_hom
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
    {𝒩 ℒ : X.left.Modules} [Invertible 𝒩] [Invertible ℒ]
    (φ : 𝒩 ⟶ ℒ) (hφ : φ ≠ 0) :
    curveDegreeOfInvertible X.hom (topologicalKrullDim_eq_one X).le 𝒩 ≤
      curveDegreeOfInvertible X.hom (topologicalKrullDim_eq_one X).le ℒ := sorry

/-- A nonzero morphism between invertible modules of equal degree on a proper curve is an
isomorphism. -/
theorem isIso_of_nonzero_hom_of_curveDegreeOfInvertible_eq
    {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
    {𝒩 ℒ : X.left.Modules} [Invertible 𝒩] [Invertible ℒ]
    (φ : 𝒩 ⟶ ℒ) (hφ : φ ≠ 0)
    (hdeg : curveDegreeOfInvertible X.hom (topologicalKrullDim_eq_one X).le 𝒩 =
      curveDegreeOfInvertible X.hom (topologicalKrullDim_eq_one X).le ℒ) :
    IsIso φ := sorry

namespace curveDegree

/-- If an invertible module on a proper, reduced, connected scheme has nonpositive degree on
every dimension-one irreducible component, then its global sections are trivial or it is
isomorphic to the structure module. -/
theorem subsingleton_sections_or_isoUnit_of_components_nonpos
    {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [IsReduced X.left]
    [ConnectedSpace X.left] (ℒ : X.left.Modules) [Invertible ℒ]
    (hcompdim :
      ∀ Z : irreducibleComponents X.left,
        topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1)
    (hdeg :
      ∀ Z : irreducibleComponents X.left,
        curveDegreeOfInvertible
          (X.left.irreducibleComponentSubschemeι Z ≫ X.hom) (hcompdim Z).le
          ((Scheme.Modules.pullback (X.left.irreducibleComponentSubschemeι Z)).obj ℒ) ≤ 0) :
    Subsingleton ℒ.sections ∨
      Nonempty (ℒ ≅ (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)) := sorry

end curveDegree

end AlgebraicGeometry.Scheme.Modules
