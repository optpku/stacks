module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Stability
public import ReasLib.AlgebraicGeometry.GroupoidScheme.SourceLocus.StandardProperties

/-!
# Cohen--Macaulay presentations of groupoid schemes

This module records the open source loci that produce Cohen--Macaulay restrictions of
flat, locally finitely presented groupoid schemes.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Canonical Cohen--Macaulay source-locus equalities imply the corresponding
largest-open statements for the source and target maps of a groupoid scheme. -/
theorem cohenMacaulayPresentationOpen_isGreatest
    {S : Scheme.{u}} (G : GroupoidScheme S) (W : Scheme.Opens G.U.left)
    (h_s : G.t.left ⁻¹ᵁ W = cohenMacaulayProperty.sourceLocus G.s.left)
    (h_t : G.s.left ⁻¹ᵁ W = cohenMacaulayProperty.sourceLocus G.t.left) :
    IsGreatest {V : Scheme.Opens G.R.left | CohenMacaulay (V.ι ≫ G.s.left)}
        (G.t.left ⁻¹ᵁ W) ∧
      IsGreatest {V : Scheme.Opens G.R.left | CohenMacaulay (V.ι ≫ G.t.left)}
        (G.s.left ⁻¹ᵁ W) := sorry

/-- The largest opens on which the source and target maps of a groupoid scheme are
Cohen--Macaulay are their canonical Cohen--Macaulay source loci. -/
theorem cohenMacaulayPresentationOpen_eq_sourceLocus
    {S : Scheme.{u}} (G : GroupoidScheme S) (W : Scheme.Opens G.U.left)
    (h_s : IsGreatest
      {V : Scheme.Opens G.R.left | CohenMacaulay (V.ι ≫ G.s.left)} (G.t.left ⁻¹ᵁ W))
    (h_t : IsGreatest
      {V : Scheme.Opens G.R.left | CohenMacaulay (V.ι ≫ G.t.left)} (G.s.left ⁻¹ᵁ W)) :
    G.t.left ⁻¹ᵁ W = cohenMacaulayProperty.sourceLocus G.s.left ∧
      G.s.left ⁻¹ᵁ W = cohenMacaulayProperty.sourceLocus G.t.left := sorry

/-- The restriction of the target map to the source inverse image of a
Cohen--Macaulay presentation open is surjective. -/
theorem cohenMacaulayPresentationTargetSurjective
    {S : Scheme.{u}} (G : GroupoidScheme S) (W : Scheme.Opens G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    (h_t : G.s.left ⁻¹ᵁ W = cohenMacaulayProperty.sourceLocus G.t.left) :
    Surjective ((G.s.left ⁻¹ᵁ W).ι ≫ G.t.left) := sorry

/-- The restriction of the source map to the target inverse image of a
Cohen--Macaulay presentation open is surjective. -/
theorem cohenMacaulayPresentationSourceSurjective
    {S : Scheme.{u}} (G : GroupoidScheme S) (W : Scheme.Opens G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    (h_s : G.t.left ⁻¹ᵁ W = cohenMacaulayProperty.sourceLocus G.s.left) :
    Surjective ((G.t.left ⁻¹ᵁ W).ι ≫ G.s.left) := sorry

/-- The source map of the canonical restriction to a Cohen--Macaulay presentation
open is Cohen--Macaulay and locally of finite presentation. -/
theorem cohenMacaulayPresentationSourceProperties
    {S : Scheme.{u}} (G : GroupoidScheme S) (W : Scheme.Opens G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    (h_s : G.t.left ⁻¹ᵁ W = cohenMacaulayProperty.sourceLocus G.s.left) :
    let U' : Over S := Over.mk (W.ι ≫ G.U.hom)
    let j : U' ⟶ G.U := Over.homMk W.ι
    CohenMacaulay (G.pullback j).s.left ∧
      LocallyOfFinitePresentation (G.pullback j).s.left := sorry

/-- The target map of the canonical restriction to a Cohen--Macaulay presentation
open is Cohen--Macaulay and locally of finite presentation. -/
theorem cohenMacaulayPresentationTargetProperties
    {S : Scheme.{u}} (G : GroupoidScheme S) (W : Scheme.Opens G.U.left)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
    (h_t : G.s.left ⁻¹ᵁ W = cohenMacaulayProperty.sourceLocus G.t.left) :
    let U' : Over S := Over.mk (W.ι ≫ G.U.hom)
    let j : U' ⟶ G.U := Over.homMk W.ι
    CohenMacaulay (G.pullback j).t.left ∧
      LocallyOfFinitePresentation (G.pullback j).t.left := sorry

/-- A flat, locally finitely presented groupoid scheme admits an object open whose
endpoint inverse images are the largest Cohen--Macaulay source opens, whose crossed
endpoint restrictions are surjective, and whose restricted structure maps are
Cohen--Macaulay and locally of finite presentation. -/
theorem existsCohenMacaulayPresentationOpen
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
    [Flat G.t.left] [LocallyOfFinitePresentation G.t.left] :
    ∃ W : Scheme.Opens G.U.left,
      IsGreatest {V : Scheme.Opens G.R.left | CohenMacaulay (V.ι ≫ G.s.left)}
          (G.t.left ⁻¹ᵁ W) ∧
        IsGreatest {V : Scheme.Opens G.R.left | CohenMacaulay (V.ι ≫ G.t.left)}
          (G.s.left ⁻¹ᵁ W) ∧
        Surjective ((G.s.left ⁻¹ᵁ W).ι ≫ G.t.left) ∧
        Surjective ((G.t.left ⁻¹ᵁ W).ι ≫ G.s.left) ∧
        (let U' : Over S := Over.mk (W.ι ≫ G.U.hom)
         let j : U' ⟶ G.U := Over.homMk W.ι
         CohenMacaulay (G.pullback j).s.left ∧
           LocallyOfFinitePresentation (G.pullback j).s.left ∧
           CohenMacaulay (G.pullback j).t.left ∧
           LocallyOfFinitePresentation (G.pullback j).t.left) := sorry

end AlgebraicGeometry.GroupoidScheme
