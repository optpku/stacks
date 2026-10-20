/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap59.Definition_59_71_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open Topology

universe u v w z

namespace CategoryTheory.Sheaf

/- Lemma 59.71.3: if a sheaf on the small étale site of a quasi-compact and
quasi-separated scheme restricts to a constructible sheaf on each member of a
constructible locally closed cover, then the original sheaf is constructible. -/
@[stacks 09YR] #check (CategoryTheory.Sheaf.isConstructibleEtale_of_constructible_cover :
    {X : Scheme.{u}} → [CompactSpace X] → [QuasiSeparatedSpace X] →
    {D : Type w} → [Category.{v} D] →
    (restrict : ∀ {Y Z : Scheme.{u}} (_ : Y ⟶ Z),
      Sheaf Z.smallEtaleTopology D → Sheaf Y.smallEtaleTopology D) →
    (finiteLocallyConstant : ∀ {Y : Scheme.{u}},
      Sheaf Y.smallEtaleTopology D → Prop) →
    (h_restrict_comp :
      ∀ {Y Z W : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ W)
        (F : Sheaf W.smallEtaleTopology D),
        Nonempty (restrict (f ≫ g) F ≅ restrict f (restrict g F))) →
    (h_finiteLocallyConstant_restrict :
      ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Sheaf Z.smallEtaleTopology D),
        finiteLocallyConstant F → finiteLocallyConstant (restrict f F)) →
    (h_finiteLocallyConstant_iso :
      ∀ {Y : Scheme.{u}} {F G : Sheaf Y.smallEtaleTopology D},
        Nonempty (F ≅ G) → finiteLocallyConstant F → finiteLocallyConstant G) →
    {ι : Type z} → (T : ι → LocallyCloseds X) →
    (hT_constructible : ∀ i, Topology.IsConstructible (T i : Set X)) →
    (hT_cover : ∀ x : X, ∃ i, x ∈ (T i : Set X)) →
    (F : Sheaf X.smallEtaleTopology D) →
    (hT : ∀ i,
      IsConstructibleEtale (fun {Y} f ↦ restrict f) finiteLocallyConstant
        (restrict (Scheme.LocallyClosedReduction.ι (T i)) F)) →
    IsConstructibleEtale (fun {Y} f ↦ restrict f) finiteLocallyConstant F)

end CategoryTheory.Sheaf
