/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.TerminalComparison
import StacksCheckRecall

/-!
# Site cohomology from hypercovering Cech representatives

The reusable owner models the statement by the filtered colimit over the homotopy refinement
category and exposes the comparison map together with its stagewise compatibility.
-/

open CategoryTheory

/- Proposition 25.10.2 (09VZ): there is a refinement-natural comparison from the filtered
colimit of Cech cohomology over terminal-presheaf hypercoverings to site cohomology whose map
at every coefficient sheaf is an isomorphism. The family universe is `max u v`, which
allows the covering refinements needed to represent site-cohomology classes. -/
@[stacks 09VZ "colimit comparison"] #check
  @HypercoveringOf.Cech.Terminal.comparison_nonempty_siteUniverse

#check @HypercoveringOf.Cech.Terminal.comparison_nonempty

/- Proposition 25.10.2 (1): relative to one fixed comparison with the filtered-colimit model,
every site-cohomology class has a representative on one hypercovering. -/
@[stacks 09VZ "existence of a representative"] #check
  @HypercoveringOf.Cech.Terminal.exists_representation

/- Proposition 25.10.2 (2): two stage representatives determine the same site-cohomology class
exactly when they agree after pullback to a common hypercovering refinement. -/
@[stacks 09VZ "equality after refinement"] #check
  @HypercoveringOf.Cech.Terminal.stageToSite_eq_iff

#check @HypercoveringOf.Cech.Terminal.Comparison
#check @HypercoveringOf.Cech.Terminal.Comparison.hom
#check @HypercoveringOf.Cech.Terminal.Comparison.stageMap_comp_hom
#check @HypercoveringOf.Cech.Terminal.stageToSite
#check @HypercoveringOf.Cech.stageMap_comp_comparison_app
#check @HypercoveringOf.Cech.Terminal.isIsomorphic_siteCohomology

-- Generic forms for arbitrary presheaf targets and any filtered refinement category.
#check @HypercoveringOf.Cech.exists_representation
#check @HypercoveringOf.Cech.stageMap_eq_stageMap_iff
