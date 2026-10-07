module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.SourceLocus.StandardProperties

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

/- Remark 40.6.3 (1): under locally finite-type hypotheses, with no flatness assumptions, the
relative-dimension-at-most-`d` source locus descends to the base-changed object scheme. -/
@[stacks 047W] #check
  (AlgebraicGeometry.GroupoidScheme.exists_open_preimage_eq_relativeDimensionLESourceLocus :
    ∀ {S U' : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      (g : U' ⟶ G.U.left) (d : ℕ)
      [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
      [LocallyOfFiniteType g],
      ∃ W : U'.Opens,
        pullback.fst g G.t.left ⁻¹ᵁ W =
          CategoryTheory.MorphismProperty.sourceLocus
            (fun _ _ f ↦ Scheme.Hom.RelativeDimensionLE f d)
            (pullback.snd g G.t.left ≫ G.s.left))

/- Remark 40.6.3 (2): under locally finite-type hypotheses, with no flatness assumptions, the
locally quasi-finite source locus descends to the base-changed object scheme. -/
@[stacks 047W] #check
  (AlgebraicGeometry.GroupoidScheme.exists_open_preimage_eq_locallyQuasiFiniteSourceLocus :
    ∀ {S U' : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      (g : U' ⟶ G.U.left)
      [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
      [LocallyOfFiniteType g],
      ∃ W : U'.Opens,
        pullback.fst g G.t.left ⁻¹ᵁ W =
          CategoryTheory.MorphismProperty.sourceLocus
            (@LocallyQuasiFinite : CategoryTheory.MorphismProperty Scheme.{u})
            (pullback.snd g G.t.left ≫ G.s.left))

/- Remark 40.6.3 (3): under locally finite-type hypotheses, with no flatness assumptions, the
unramified source locus descends to the base-changed object scheme. -/
@[stacks 047W] #check
  (AlgebraicGeometry.GroupoidScheme.exists_open_preimage_eq_unramifiedSourceLocus :
    ∀ {S U' : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      (g : U' ⟶ G.U.left)
      [LocallyOfFiniteType G.s.left] [LocallyOfFiniteType G.t.left]
      [LocallyOfFiniteType g],
      ∃ W : U'.Opens,
        pullback.fst g G.t.left ⁻¹ᵁ W =
          CategoryTheory.MorphismProperty.sourceLocus
            (@Unramified : CategoryTheory.MorphismProperty Scheme.{u})
            (pullback.snd g G.t.left ≫ G.s.left))

/- Remark 40.6.3 (4): for flat locally finitely presented source and target maps and a locally
finitely presented base-change map, the flat source locus descends to the base-changed object
scheme. -/
@[stacks 047W] #check
  (AlgebraicGeometry.GroupoidScheme.exists_open_preimage_eq_flatSourceLocus_of_locallyOfFinitePresentation :
    ∀ {S U' : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      (g : U' ⟶ G.U.left)
      [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
      [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
      [LocallyOfFinitePresentation g],
      ∃ W : U'.Opens,
        pullback.fst g G.t.left ⁻¹ᵁ W =
          CategoryTheory.MorphismProperty.sourceLocus
            (@Flat : CategoryTheory.MorphismProperty Scheme.{u})
            (pullback.snd g G.t.left ≫ G.s.left))

/- Remark 40.6.3 (5): for flat locally finitely presented source and target maps and a locally
finitely presented base-change map, the Cohen--Macaulay source locus descends to the base-changed
object scheme. -/
@[stacks 047W] #check
  (AlgebraicGeometry.GroupoidScheme.exists_open_preimage_eq_cohenMacaulaySourceLocus :
    ∀ {S U' : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      (g : U' ⟶ G.U.left)
      [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
      [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
      [LocallyOfFinitePresentation g],
      ∃ W : U'.Opens,
        pullback.fst g G.t.left ⁻¹ᵁ W =
          CategoryTheory.MorphismProperty.sourceLocus
            (@CohenMacaulay : CategoryTheory.MorphismProperty Scheme.{u})
            (pullback.snd g G.t.left ≫ G.s.left))

/- Remark 40.6.3 (6): for flat locally finitely presented source and target maps and a locally
finitely presented base-change map, the syntomic source locus descends to the base-changed object
scheme. -/
@[stacks 047W] #check
  (AlgebraicGeometry.GroupoidScheme.exists_open_preimage_eq_syntomicSourceLocus :
    ∀ {S U' : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      (g : U' ⟶ G.U.left)
      [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
      [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
      [LocallyOfFinitePresentation g],
      ∃ W : U'.Opens,
        pullback.fst g G.t.left ⁻¹ᵁ W =
          CategoryTheory.MorphismProperty.sourceLocus
            (@Syntomic : CategoryTheory.MorphismProperty Scheme.{u})
            (pullback.snd g G.t.left ≫ G.s.left))

/- Remark 40.6.3 (7): for flat locally finitely presented source and target maps and a locally
finitely presented base-change map, the smooth source locus descends to the base-changed object
scheme. -/
@[stacks 047W] #check
  (AlgebraicGeometry.GroupoidScheme.exists_open_preimage_eq_smoothSourceLocus :
    ∀ {S U' : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      (g : U' ⟶ G.U.left)
      [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
      [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
      [LocallyOfFinitePresentation g],
      ∃ W : U'.Opens,
        pullback.fst g G.t.left ⁻¹ᵁ W =
          CategoryTheory.MorphismProperty.sourceLocus
            (@Smooth : CategoryTheory.MorphismProperty Scheme.{u})
            (pullback.snd g G.t.left ≫ G.s.left))

/- Remark 40.6.3 (8): for flat locally finitely presented source and target maps and a locally
finitely presented base-change map, the étale source locus descends to the base-changed object
scheme. -/
@[stacks 047W] #check
  (AlgebraicGeometry.GroupoidScheme.exists_open_preimage_eq_etaleSourceLocus :
    ∀ {S U' : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      (g : U' ⟶ G.U.left)
      [Flat G.s.left] [LocallyOfFinitePresentation G.s.left]
      [Flat G.t.left] [LocallyOfFinitePresentation G.t.left]
      [LocallyOfFinitePresentation g],
      ∃ W : U'.Opens,
        pullback.fst g G.t.left ⁻¹ᵁ W =
          CategoryTheory.MorphismProperty.sourceLocus
            (@Etale : CategoryTheory.MorphismProperty Scheme.{u})
            (pullback.snd g G.t.left ≫ G.s.left))
