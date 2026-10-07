module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A scheme morphism is integral exactly when some affine open cover of the target has affine
preimages and induces integral maps on global sections. -/
theorem isIntegralHom_iff_exists_affineOpenCover :
    IsIntegralHom f ↔
      ∃ 𝒰 : S.AffineOpenCover.{u},
        ∀ i : 𝒰.I₀,
          IsAffine (f ⁻¹ᵁ (𝒰.f i).opensRange) ∧
            (CommRingCat.Hom.hom
              (Scheme.Hom.appTop (f ∣_ (𝒰.f i).opensRange))).IsIntegral := by
  constructor
  · intro hf
    refine ⟨S.affineOpenCover, ?_⟩
    have h :=
      (HasAffineProperty.iff_of_iSup_eq_top (P := @IsIntegralHom) (f := f)
        (fun i ↦ ⟨(S.affineOpenCover.f i).opensRange, isAffineOpen_opensRange _⟩)
        S.affineOpenCover.openCover.iSup_opensRange).1 hf
    intro i
    exact ⟨(h i).1, (h i).2⟩
  · rintro ⟨𝒰, h𝒰⟩
    apply
      (HasAffineProperty.iff_of_iSup_eq_top (P := @IsIntegralHom) (f := f)
        (fun i ↦ ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange _⟩)
        𝒰.openCover.iSup_opensRange).2
    intro i
    exact ⟨(h𝒰 i).1, (h𝒰 i).2⟩

/-- A scheme morphism is integral exactly when it is integral after restriction along every member
of some open cover of the target. -/
theorem isIntegralHom_iff_exists_openCover :
    IsIntegralHom f ↔
      ∃ 𝒰 : S.OpenCover.{u},
        ∀ i : 𝒰.I₀, IsIntegralHom (f ∣_ (𝒰.f i).opensRange) := by
  constructor
  · intro hf
    refine ⟨S.affineOpenCover.openCover, ?_⟩
    exact
      (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsIntegralHom) (f := f)
        (fun i ↦ (S.affineOpenCover.openCover.f i).opensRange)
        S.affineOpenCover.openCover.iSup_opensRange).1 hf
  · rintro ⟨𝒰, h𝒰⟩
    exact
      (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsIntegralHom) (f := f)
        (fun i ↦ (𝒰.f i).opensRange) 𝒰.iSup_opensRange).2 h𝒰

end AlgebraicGeometry
