/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Resolution
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.59.10: K-flat resolutions

@stack 06Y4
-/

/- Lemma 15.59.10, tag `06Y4`: every complex of `R`-modules has a termwise-surjective
quasi-isomorphism from a K-flat complex with flat terms. -/
@[stacks 06Y4 "K-flat resolution"]
#check @CochainComplex.exists_termwiseEpi_kFlatResolution

/- The same resolution expressed using the categorical epimorphism on complexes. -/
#check @CochainComplex.exists_epi_kFlatResolution

/- The canonical resolution conditions consumed by K-flat localization. -/
#check @ModuleCat.KFlat.hasResolutions
#check @ModuleCat.KFlat.TermwiseFlat.hasResolutions
