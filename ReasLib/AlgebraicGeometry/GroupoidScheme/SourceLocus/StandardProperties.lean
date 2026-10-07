module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.FlatSourceLocus
public import ReasLib.AlgebraicGeometry.GroupoidScheme.SourceLocus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CohenMacaulay.Locus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.LocalAtSource
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Locus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Locality

/-!
# Standard source loci for groupoid schemes

This module specializes source-locus descent for groupoid schemes to standard properties of
scheme morphisms.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Under locally finite-type hypotheses alone, the bounded-relative-dimension source locus
after base change descends to an open in the base-changed object scheme. -/
theorem exists_open_preimage_eq_relativeDimensionLESourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left) (d : ℕ)
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
    [LocallyOfFiniteType g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (fun _ _ f ↦ Scheme.Hom.RelativeDimensionLE f d)
          (pullback.snd g G.t.left ≫ G.s.left) := sorry

/-- Under locally finite-type hypotheses alone, the locally quasi-finite source locus after
base change descends to an open in the base-changed object scheme. -/
theorem exists_open_preimage_eq_locallyQuasiFiniteSourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
    [LocallyOfFiniteType g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@LocallyQuasiFinite : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := sorry

/-- Under locally finite-type hypotheses alone, the unramified source locus after base change
descends to an open in the base-changed object scheme. -/
theorem exists_open_preimage_eq_unramifiedSourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
    [LocallyOfFiniteType g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@Unramified : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := sorry

/-- If the source and target maps are flat and locally of finite presentation and the base-change
map is locally of finite presentation, then the flat source locus descends to an open in the
base-changed object scheme. -/
theorem exists_open_preimage_eq_flatSourceLocus_of_locallyOfFinitePresentation
    {S U' : Scheme.{u}} (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    [LocallyOfFinitePresentation g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@Flat : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := sorry

/-- If the source and target maps are flat and locally of finite presentation and the base-change
map is locally of finite presentation, then the Cohen--Macaulay source locus descends to an open
in the base-changed object scheme. -/
theorem exists_open_preimage_eq_cohenMacaulaySourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    [LocallyOfFinitePresentation g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@CohenMacaulay : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := sorry

/-- If the source and target maps are flat and locally of finite presentation and the base-change
map is locally of finite presentation, then the syntomic source locus descends to an open in the
base-changed object scheme. -/
theorem exists_open_preimage_eq_syntomicSourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    [LocallyOfFinitePresentation g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@Syntomic : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := sorry

/-- If the source and target maps are flat and locally of finite presentation and the base-change
map is locally of finite presentation, then the smooth source locus descends to an open in the
base-changed object scheme. -/
theorem exists_open_preimage_eq_smoothSourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    [LocallyOfFinitePresentation g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@Smooth : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := sorry

/-- If the source and target maps are flat and locally of finite presentation and the base-change
map is locally of finite presentation, then the étale source locus descends to an open in the
base-changed object scheme. -/
theorem exists_open_preimage_eq_etaleSourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S) (g : U' ⟶ G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    [LocallyOfFinitePresentation g] :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        CategoryTheory.MorphismProperty.sourceLocus
          (@Etale : CategoryTheory.MorphismProperty Scheme.{u})
          (pullback.snd g G.t.left ≫ G.s.left) := sorry

end AlgebraicGeometry.GroupoidScheme
