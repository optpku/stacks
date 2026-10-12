/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.Presentation
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The residue sequence of a punctured line bundle

This file defines the residue sequence associated to an explicit presentation of the
weight-zero de Rham complex of a punctured line bundle and states its exactness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle

variable {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules)
variable [Scheme.Modules.Invertible ℒ]
variable (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
variable [Scheme.IsRelativeSpectrumOver P]

/-- The weight-zero pushed-forward de Rham complex selected by an explicit presentation. -/
noncomputable abbrev degreeZeroComplex (D : WeightZeroDeRham f ℒ P) :
    CochainComplex (Modules f.toLRSHom.toShHom) ℤ :=
  D.complex

/-- The inclusion of the selected weight-zero complex into all pushed-forward forms. -/
noncomputable abbrev zeroInclusion (D : WeightZeroDeRham f ℒ P) :
    degreeZeroComplex f ℒ P D ⟶ pushedForwardDeRham f ℒ P :=
  D.zeroInclusion

/-- The degree-`p` weight-zero homogeneous summand as a subobject of the pushed-forward
forms. -/
noncomputable def degreeZeroForm (D : WeightZeroDeRham f ℒ P) (p : ℤ) :
    Subobject ((pushedForwardDeRham f ℒ P).X p) :=
  @Subobject.mk _ _ _ _ _ (D.zeroInclusion_mono p)

/-- The inclusion of ordinary relative forms into the selected weight-zero complex. -/
noncomputable abbrev ordinaryInclusion (D : WeightZeroDeRham f ℒ P) :
    ordinaryComplex f ⟶ degreeZeroComplex f ℒ P D :=
  D.ordinaryInclusion

/-- The inclusion of ordinary forms agrees, after the homogeneous inclusion, with the
functorial map to all pushed-forward forms. -/
theorem ordinaryInclusion_zeroInclusion (D : WeightZeroDeRham f ℒ P) :
    ordinaryInclusion f ℒ P D ≫ zeroInclusion f ℒ P D =
      ordinaryToPushedForward f ℒ P := sorry

/-- The residue morphism from the selected weight-zero complex to ordinary forms shifted
by `-1`. -/
noncomputable abbrev residue (D : WeightZeroDeRham f ℒ P) :
    degreeZeroComplex f ℒ P D ⟶ (ordinaryComplex f)⟦(-1 : ℤ)⟧ :=
  D.residue

/-- Inclusion of ordinary forms followed by residue is zero. -/
theorem inclusion_residue (D : WeightZeroDeRham f ℒ P) :
    ordinaryInclusion f ℒ P D ≫ residue f ℒ P D = 0 := sorry

/-- The residue short complex
`Ωᵧ_[X/S] ⟶ Ωᵧ_[L⋆/S, 0] ⟶ Ωᵧ_[X/S]⟦-1⟧`. -/
noncomputable def sequence (D : WeightZeroDeRham f ℒ P) :
    ShortComplex (CochainComplex (Modules f.toLRSHom.toShHom) ℤ) :=
  ShortComplex.mk (ordinaryInclusion f ℒ P D) (residue f ℒ P D)
    (inclusion_residue f ℒ P D)

/-- The first term of the residue sequence is the ordinary relative de Rham complex. -/
theorem sequence_X₁ (D : WeightZeroDeRham f ℒ P) :
    (sequence f ℒ P D).X₁ = ordinaryComplex f := sorry

/-- The middle term of the residue sequence is the selected weight-zero pushed-forward de
Rham complex. -/
theorem sequence_X₂ (D : WeightZeroDeRham f ℒ P) :
    (sequence f ℒ P D).X₂ = degreeZeroComplex f ℒ P D := sorry

/-- The third term is the ordinary relative de Rham complex shifted by `-1`. -/
theorem sequence_X₃ (D : WeightZeroDeRham f ℒ P) :
    (sequence f ℒ P D).X₃ = (ordinaryComplex f)⟦(-1 : ℤ)⟧ := sorry

/-- Locally, residue sends `dlog(s) ∧ ω` to `ω` under the shift identification. -/
theorem residue_local_formula (D : WeightZeroDeRham f ℒ P)
    (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
    (s : RingedSpace.stalkModuleCat ℒ x) (h_s : IsStalkGenerator ℒ x s) :
    D.dlogWedge q p h_qp x s h_s ≫
        (stalkFunctor f x).map (D.residue.f p) =
      (shiftedFormIso f q p h_qp x).inv := sorry

/-- The local direct-sum formula is compatible with replacing one generator of `ℒ` by
another. -/
theorem dlogWedge_changeGenerator (D : WeightZeroDeRham f ℒ P)
    (q p : ℤ) (h_qp : q = p + (-1 : ℤ)) (x : X)
    (s t : RingedSpace.stalkModuleCat ℒ x)
    (h_s : IsStalkGenerator ℒ x s) (h_t : IsStalkGenerator ℒ x t) :
    ∃ correction :
        (stalkFunctor f x).obj ((ordinaryComplex f).X q) ⟶
          (stalkFunctor f x).obj ((ordinaryComplex f).X p),
      D.dlogWedge q p h_qp x s h_s =
        correction ≫ (stalkFunctor f x).map (D.ordinaryInclusion.f p) +
          D.dlogWedge q p h_qp x t h_t := sorry

end AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle

/-- The residue sequence associated to an explicit weight-zero presentation of a punctured
line bundle is short exact. -/
theorem puncturedLineBundleSequence_shortExact
    {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
    [Scheme.IsRelativeSpectrumOver P]
    (D : RingedSpace.DeRham.PuncturedLineBundle.WeightZeroDeRham f ℒ P) :
    (RingedSpace.DeRham.PuncturedLineBundle.sequence f ℒ P D).ShortExact := sorry
