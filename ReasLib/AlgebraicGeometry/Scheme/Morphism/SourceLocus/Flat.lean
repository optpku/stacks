module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.EtaleLocal.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus

/-!
# Flat source loci

This module records the compatibility of the flat source locus with cartesian squares whose base
morphism is flat and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- In a cartesian square whose base morphism is flat and locally of finite presentation, the flat
source locus of the upper horizontal morphism is the preimage of the flat source locus of the
lower horizontal morphism. -/
theorem flatSourceLocus_preimage_of_isPullback
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {b : Y' ⟶ Y}
    {p : X' ⟶ X} {f' : X' ⟶ Y'} [Flat b] [LocallyOfFinitePresentation b]
    (sq : IsPullback p f' f b) :
    p ⁻¹ᵁ CategoryTheory.MorphismProperty.sourceLocus
      (@Flat : MorphismProperty Scheme.{u}) f =
      CategoryTheory.MorphismProperty.sourceLocus
        (@Flat : MorphismProperty Scheme.{u}) f' := by
  ext x'
  constructor
  · intro hx'
    change p x' ∈
      CategoryTheory.MorphismProperty.sourceLocus
        (@Flat : MorphismProperty Scheme.{u}) f at hx'
    rw [CategoryTheory.MorphismProperty.mem_sourceLocus] at hx'
    rcases hx' with ⟨U, hxU, hU⟩
    refine
      (CategoryTheory.MorphismProperty.mem_sourceLocus
        (@Flat : MorphismProperty Scheme.{u}) f' x').2 ?_
    refine ⟨p ⁻¹ᵁ U, hxU, ?_⟩
    have hpbU :
        IsPullback
          (p.resLE U (p ⁻¹ᵁ U) le_rfl)
          (f'.resLE ⊤ (p ⁻¹ᵁ U) (by simp))
          (f.resLE ⊤ U (by simp))
          (b.resLE ⊤ ⊤ le_rfl) := by
      simpa using
        (Scheme.Hom.isPullback_resLE (H := sq)
          (US := ⊤) (UT := ⊤) (UX := U)
          (hUST := le_rfl) (hUSX := by simp)
          (UY := p ⁻¹ᵁ U)
          (hUY := by simp))
    have hUresComp : Flat (f.resLE ⊤ U (by simp) ≫ Y.topIso.hom) := by
      simpa using hU
    have hUres : Flat (f.resLE ⊤ U (by simp)) :=
      (CategoryTheory.MorphismProperty.cancel_right_of_respectsIso
        (@Flat : MorphismProperty Scheme.{u})
        (f.resLE ⊤ U (by simp)) Y.topIso.hom).mp hUresComp
    have hU' : Flat (f'.resLE ⊤ (p ⁻¹ᵁ U) (by simp)) :=
      CategoryTheory.MorphismProperty.of_isPullback
        (P := (@Flat : MorphismProperty Scheme.{u})) hpbU hUres
    have hU'comp : Flat (f'.resLE ⊤ (p ⁻¹ᵁ U) (by simp) ≫ Y'.topIso.hom) := by
      exact CategoryTheory.MorphismProperty.comp_mem
        (@Flat : MorphismProperty Scheme.{u})
        (f'.resLE ⊤ (p ⁻¹ᵁ U) (by simp)) Y'.topIso.hom hU' inferInstance
    simpa using hU'comp
  · intro hx'
    change p x' ∈
      CategoryTheory.MorphismProperty.sourceLocus
        (@Flat : MorphismProperty Scheme.{u}) f
    rcases
      (CategoryTheory.MorphismProperty.mem_sourceLocus
        (@Flat : MorphismProperty Scheme.{u}) f' x').1 hx' with
      ⟨V, hxV, hV⟩
    let xV : V.toScheme := ⟨x', hxV⟩
    have hcompEq : (V.ι ≫ p) ≫ f = (V.ι ≫ f') ≫ b := by
      simpa [Category.assoc] using congrArg (fun k => V.ι ≫ k) sq.w
    have hcomp : Flat ((V.ι ≫ p) ≫ f) := by
      rw [hcompEq]
      exact CategoryTheory.MorphismProperty.comp_mem
        (@Flat : MorphismProperty Scheme.{u})
        (V.ι ≫ f') b hV inferInstance
    -- Local instance justification (proof-local temporary data): supplies the composition law
    -- required by the fppf source-locality theorem in this proof.
    let _ :
        CategoryTheory.MorphismProperty.RespectsLeft
          (@Flat : MorphismProperty Scheme.{u})
          ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) :=
      { precomp := fun i hi g hg ↦
          CategoryTheory.MorphismProperty.comp_mem
            (@Flat : MorphismProperty Scheme.{u}) i g hi.1 hg }
    -- Local instance justification (proof-local temporary data): refines the available fpqc
    -- descent input to the fppf precomposition property needed below.
    let _ :
        (CategoryTheory.MorphismProperty.inverseImage
          (@Flat : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme).HasOfPrecompProperty
          (CategoryTheory.MorphismProperty.inverseImage
            (((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation ⊓
              @Surjective) : MorphismProperty Scheme.{u})
            AffineScheme.forgetToScheme) :=
      CategoryTheory.MorphismProperty.HasOfPrecompProperty.of_le
        (W := CategoryTheory.MorphismProperty.inverseImage
          (@Flat : MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)
        (Q := CategoryTheory.MorphismProperty.inverseImage
          (((@Flat : MorphismProperty Scheme.{u}) ⊓ @Surjective) :
            MorphismProperty Scheme.{u})
          AffineScheme.forgetToScheme)
        (by
          intro T₁ T₂ g hg
          exact ⟨hg.1.1, hg.2⟩)
    -- Local instance justification (proof-local temporary data): records flatness of the
    -- pullback projection supplied by the cartesian-square hypothesis.
    let _ : Flat p :=
      CategoryTheory.MorphismProperty.of_isPullback
        (P := (@Flat : MorphismProperty Scheme.{u})) sq.flip inferInstance
    -- Local instance justification (proof-local temporary data): records finite presentation of
    -- the pullback projection supplied by the cartesian-square hypothesis.
    let _ : LocallyOfFinitePresentation p :=
      CategoryTheory.MorphismProperty.of_isPullback
        (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
        sq.flip inferInstance
    -- Local instance justification (proof-local temporary data): supplies flatness of the
    -- composite used in the source-locus pullback calculation.
    let _ : Flat (V.ι ≫ p) :=
      CategoryTheory.MorphismProperty.comp_mem
        (@Flat : MorphismProperty Scheme.{u}) V.ι p inferInstance inferInstance
    -- Local instance justification (proof-local temporary data): supplies finite presentation of
    -- the composite used in the source-locus pullback calculation.
    let _ : LocallyOfFinitePresentation (V.ι ≫ p) :=
      CategoryTheory.MorphismProperty.comp_mem
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
        V.ι p inferInstance inferInstance
    -- Local instance justification (proof-local temporary data): packages the established fppf
    -- locality theorem in the exact typeclass form consumed by `sourceLocus_preimage_fppf`.
    let _ :
        CategoryTheory.MorphismProperty.IsLocalAtSource
          (@Flat : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage := by
      exact AlgebraicGeometry.Scheme.MorphismProperty.fppfLocalAtSource
        (@Flat : MorphismProperty Scheme.{u})
    have hpreimage :
        (V.ι ≫ p) ⁻¹ᵁ
            CategoryTheory.MorphismProperty.sourceLocus
              (@Flat : MorphismProperty Scheme.{u}) f =
          CategoryTheory.MorphismProperty.sourceLocus
            (@Flat : MorphismProperty Scheme.{u}) ((V.ι ≫ p) ≫ f) := by
      simpa using
        (CategoryTheory.MorphismProperty.sourceLocus_preimage_fppf
          (@Flat : MorphismProperty Scheme.{u}) f (V.ι ≫ p))
    have htop :
        CategoryTheory.MorphismProperty.sourceLocus
            (@Flat : MorphismProperty Scheme.{u}) ((V.ι ≫ p) ≫ f) = ⊤ := by
      rw [CategoryTheory.MorphismProperty.sourceLocus_eq_top_iff]
      exact hcomp
    have hxVpre :
        xV ∈
          (V.ι ≫ p) ⁻¹ᵁ
            CategoryTheory.MorphismProperty.sourceLocus
              (@Flat : MorphismProperty Scheme.{u}) f := by
      rw [hpreimage, htop]
      simp [xV]
    simpa [xV] using hxVpre

end AlgebraicGeometry.Scheme.Hom
