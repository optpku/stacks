module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.SourceLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus.Flat

/-!
# Flat source loci for groupoid schemes

This module specializes source-locus descent for groupoid schemes to flat morphisms.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- If the source and target maps of a groupoid scheme are flat and locally of finite
presentation, then the flat source locus after any base change is the preimage of an open in the
base-changed object scheme. -/
theorem exists_open_preimage_eq_flatSourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left) [Flat G.s.left]
    [LocallyOfFinitePresentation G.s.left] [Flat G.t.left]
    [LocallyOfFinitePresentation G.t.left] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@Flat : MorphismProperty Scheme.{u}) (pullback.snd g G.t.left ≫ G.s.left) := by
  refine exists_open_preimage_eq_sourceLocus (G := G) (g := g)
      (@Flat : MorphismProperty Scheme.{u}) ⊤
      ((@Flat ⊓ @LocallyOfFinitePresentation) : MorphismProperty Scheme.{u})
      ?_ ?_ ?_ ?_ ?_ ?_
  · intro X Y f hf
    trivial
  · intro X Y f hf
    -- Local instance justification (proof-local temporary data): transports the established
    -- étale-locality instance to the standard-topology precoverage expected by the generic API.
    let _ :
        CategoryTheory.MorphismProperty.IsLocalAtSource
          (@Flat : MorphismProperty Scheme.{u}) StandardTopology.etale.precoverage := by
      simpa [StandardTopology.precoverage] using
        (inferInstance :
          CategoryTheory.MorphismProperty.IsLocalAtSource
            (@Flat : MorphismProperty Scheme.{u}) Scheme.etalePrecoverage)
    have hne : StandardTopology.etale ≠ StandardTopology.zariski := by
      intro h
      cases h
    simpa using
      (CategoryTheory.MorphismProperty.sourceLocus_isGreatest_nonZariski
        (@Flat : MorphismProperty Scheme.{u}) .etale hne f)
  · intro X Y X' Y' f b p f' hf hb hpb
    rcases hb with ⟨hbFlat, hbLfp⟩
    -- Local instance justification (proof-local temporary data): exposes the flat component of
    -- the explicit conjunction supplied by the generic descent theorem.
    let _ : Flat b := hbFlat
    -- Local instance justification (proof-local temporary data): exposes the finite-presentation
    -- component of the explicit conjunction supplied by the generic descent theorem.
    let _ : LocallyOfFinitePresentation b := hbLfp
    simpa using Scheme.Hom.flatSourceLocus_preimage_of_isPullback
      (f := f) (b := b) (p := p) (f' := f') hpb
  · exact ⟨inferInstance, inferInstance⟩
  · exact ⟨inferInstance, inferInstance⟩
  · trivial

end AlgebraicGeometry.GroupoidScheme
