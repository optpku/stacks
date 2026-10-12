/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Sections

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.44.12 (1): a nonzero section of an invertible module on a proper curve forces
nonnegative degree. -/
@[stacks 0B40] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegreeOfInvertible_nonneg_of_nonzero_section :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
      {ℒ : X.left.Modules} [Scheme.Modules.Invertible ℒ]
      (s : ℒ.sections) (_ : ℒ.unitHomEquiv.symm s ≠ 0),
      0 ≤ Scheme.Modules.curveDegreeOfInvertible X.hom
        (topologicalKrullDim_eq_one X).le ℒ)

/- Lemma 33.44.12 (2): a nonzero section of an invertible module on a proper curve whose zero
scheme is nonempty forces positive degree. -/
@[stacks 0B40] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegreeOfInvertible_pos_of_nonzero_section_of_nonempty_zeroScheme :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
      {ℒ : X.left.Modules} [Scheme.Modules.Invertible ℒ]
      (s : ℒ.sections) (_ : ℒ.unitHomEquiv.symm s ≠ 0)
      (_ : Nonempty (Scheme.zeroScheme ℒ s)),
      0 < Scheme.Modules.curveDegreeOfInvertible X.hom
        (topologicalKrullDim_eq_one X).le ℒ)

/- Lemma 33.44.12 (3): nonzero sections of an invertible module and its inverse tensor power
on a proper curve force the module to be isomorphic to the structure module. -/
@[stacks 0B40] #check
  (AlgebraicGeometry.Scheme.Modules.isoUnit_of_nonzero_section_of_nonzero_section_inverse :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
      {ℒ : X.left.Modules} [Scheme.Modules.Invertible ℒ]
      (s : ℒ.sections) (_ : ℒ.unitHomEquiv.symm s ≠ 0)
      (t : (Scheme.Modules.tensorPowerInt ℒ (-1)).sections)
      (_ : (Scheme.Modules.tensorPowerInt ℒ (-1)).unitHomEquiv.symm t ≠ 0),
      Nonempty
        (ℒ ≅ (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)))

/- Lemma 33.44.12 (4): a nonzero section of a nonpositive-degree invertible module on a proper
curve forces the module to be isomorphic to the structure module. -/
@[stacks 0B40] #check
  (AlgebraicGeometry.Scheme.Modules.isoUnit_of_curveDegreeOfInvertible_nonpos_of_nonzero_section :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
      {ℒ : X.left.Modules} [Scheme.Modules.Invertible ℒ]
      (_ : Scheme.Modules.curveDegreeOfInvertible X.hom
        (topologicalKrullDim_eq_one X).le ℒ ≤ 0)
      (s : ℒ.sections) (_ : ℒ.unitHomEquiv.symm s ≠ 0),
      Nonempty
        (ℒ ≅ (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)))

/- Lemma 33.44.12 (5): a nonzero morphism of invertible modules on a proper curve weakly
increases degree. -/
@[stacks 0B40] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegreeOfInvertible_le_curveDegreeOfInvertible_of_nonzero_hom :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
      {𝒩 ℒ : X.left.Modules} [Scheme.Modules.Invertible 𝒩] [Scheme.Modules.Invertible ℒ]
      (φ : 𝒩 ⟶ ℒ) (_ : φ ≠ 0),
      Scheme.Modules.curveDegreeOfInvertible X.hom
          (topologicalKrullDim_eq_one X).le 𝒩 ≤
        Scheme.Modules.curveDegreeOfInvertible X.hom
          (topologicalKrullDim_eq_one X).le ℒ)

/- Lemma 33.44.12 (6): a nonzero morphism of equal-degree invertible modules on a proper curve
is an isomorphism. -/
@[stacks 0B40] #check
  (AlgebraicGeometry.Scheme.Modules.isIso_of_nonzero_hom_of_curveDegreeOfInvertible_eq :
    ∀ {k : Type u} [Field k]
      (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
      {𝒩 ℒ : X.left.Modules} [Scheme.Modules.Invertible 𝒩] [Scheme.Modules.Invertible ℒ]
      (φ : 𝒩 ⟶ ℒ) (_ : φ ≠ 0)
      (_ : Scheme.Modules.curveDegreeOfInvertible X.hom
          (topologicalKrullDim_eq_one X).le 𝒩 =
        Scheme.Modules.curveDegreeOfInvertible X.hom
          (topologicalKrullDim_eq_one X).le ℒ),
      IsIso φ)
