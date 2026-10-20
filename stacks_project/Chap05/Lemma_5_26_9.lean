/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.Stonean.Minimal
import StacksCheckRecall

@[expose] public section

open CategoryTheory Set

universe u

/- Lemma 5.26.9 (1): the canonical Stonean presentation is surjective. -/
@[stacks 090D "canonical Stonean presentation is surjective"]
#check (fun X : CompHaus.{u} ↦
  (CompHaus.epi_iff_surjective (CompHaus.presentation.π X)).mp
    (inferInstance : Epi (CompHaus.presentation.π X)))

/- The shared lift bridge accepts the map-level surjectivity used by the source statement. -/
#check CompHaus.liftOfSurjective

/- Lemma 5.26.9 (2): the source's two minimality hypotheses assemble into two
`MinimalStoneanCover` values, whose canonical comparison is a homeomorphism. -/
@[stacks 090D "uniqueness of minimal Stonean covers up to isomorphism"]
#check (fun {X : CompHaus.{u}} {Y Z : Stonean.{u}}
  {f : Y.compHaus ⟶ X} {g : Z.compHaus ⟶ X}
  (hf_surj : Function.Surjective f) (hg_surj : Function.Surjective g)
  (hf_min : ∀ E : Set Y, E ≠ (Set.univ : Set Y) → IsClosed E → f '' E ≠ (Set.univ : Set X))
  (hg_min : ∀ E : Set Z, E ≠ (Set.univ : Set Z) → IsClosed E → g '' E ≠ (Set.univ : Set X)) ↦
  Nonempty.intro (CompHaus.MinimalStoneanCover.homeomorph
    { space := Y, π := f, minimal := ⟨hf_surj, hf_min⟩ }
    { space := Z, π := g, minimal := ⟨hg_surj, hg_min⟩ }))
