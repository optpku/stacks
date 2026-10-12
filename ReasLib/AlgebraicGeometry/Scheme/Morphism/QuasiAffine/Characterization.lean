/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Operations
public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Characterization
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Pushforward

/-!
# Characterizations of quasi-affine scheme morphisms

This file characterizes quasi-affine morphisms by affine open covers and by
quasi-compact open immersions into relative spectra.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A morphism admits a quasi-compact open immersion into a relative spectrum
of the pushforward of its structure sheaf via the canonical morphism. -/
def HasQuasiCompactOpenImmersionToPushforwardRelativeSpectrum
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∃ (hqc : QuasiCompact f) (hqs : QuasiSeparated f)
      (P : Scheme.RelativeSpectrumOver
        (@Scheme.pushforwardStructureSheafQcAlgebra _ _ f hqc hqs))
      (hP : Scheme.IsRelativeSpectrumOver P),
    let canonicalMap :=
      @Scheme.pushforwardStructureSheafRelativeSpectrumHom _ _ f hqc hqs P hP
    QuasiCompact canonicalMap ∧
      IsOpenImmersion canonicalMap ∧
      canonicalMap ≫ Scheme.relativeSpecπ P = f

/-- A morphism is quasi-affine exactly when this can be checked on the
members of some affine open cover of its target. -/
theorem quasiAffineHom_iff_exists_affineOpenCover
    {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiAffineHom f ↔
      ∃ cover : S.AffineOpenCover,
        ∀ i : cover.I₀, ((cover.openCover.pullback₁ f).X i).IsQuasiAffine := sorry

/-- A morphism is quasi-affine exactly when it admits a quasi-compact open
immersion over the target into a relative spectrum of a quasi-coherent algebra. -/
theorem quasiAffineHom_iff_exists_relativeSpectrum_quasiCompact_openImmersion
    {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiAffineHom f ↔
      ∃ (A : S.QcAlgebraUnder) (P : Scheme.RelativeSpectrumOver A),
        Scheme.IsRelativeSpectrumOver P ∧
          ∃ j : X ⟶ Scheme.relativeSpec P,
            QuasiCompact j ∧ IsOpenImmersion j ∧
              j ≫ Scheme.relativeSpecπ P = f := sorry

/-- A morphism is quasi-affine exactly when its canonical morphism to a
relative spectrum of the pushforward of its structure sheaf is a
quasi-compact open immersion. -/
theorem QuasiAffineHom.iff_pushforwardRelativeSpectrum
    {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiAffineHom f ↔
      HasQuasiCompactOpenImmersionToPushforwardRelativeSpectrum f := sorry

/-- Quasi-affineness, its affine-cover criterion, a relative-spectrum
presentation, and the canonical pushforward-relative-spectrum criterion are
equivalent. -/
theorem quasiAffineHom_tfae {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE [
      QuasiAffineHom f,
      ∃ cover : S.AffineOpenCover,
        ∀ i : cover.I₀, ((cover.openCover.pullback₁ f).X i).IsQuasiAffine,
      ∃ (A : S.QcAlgebraUnder) (P : Scheme.RelativeSpectrumOver A),
        Scheme.IsRelativeSpectrumOver P ∧
          ∃ j : X ⟶ Scheme.relativeSpec P,
            QuasiCompact j ∧ IsOpenImmersion j ∧
              j ≫ Scheme.relativeSpecπ P = f,
      HasQuasiCompactOpenImmersionToPushforwardRelativeSpectrum f] := sorry

end AlgebraicGeometry
