/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Godement.BoundedBelow
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open ComplexShape HomologicalComplex
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace.Godement

/- [stacks 0FKT] Lemma 20.30.2: Let `X` be a ringed space and let `F` be a
bounded-below complex of `𝒪_X`-modules.  There exist a bounded-below complex
`G` of `𝒪_X`-modules and a quasi-isomorphism `F ⟶ G` such that every term of
`G` is flasque.  For every point `x : X`, the induced morphism on stalk
complexes is a chain homotopy equivalence.

The reusable owner is `Godement.Total.replacement`: its target is bounded below,
termwise flasque, and its comparison map has both the quasi-isomorphism and
stalkwise homotopy-equivalence properties.  The existential form is exposed by
`exists_flasqueResolution`. -/
#check @flasque
#check @Flasque
#check @Total.input
#check @Total.finiteSupport
#check @Total.lowerBound
#check @Total.termwiseFlasque
#check @Total.plus
#check @Total.term_isFlasque
#check @Total.toPlus
#check @Total.toFlasque
#check @Total.replacement
#check @Total.flasqueReplacement
#check @Total.comparison
#check @Total.comparisonMap
#check @Total.comparison_quasiIso
#check @Total.stalkComparison
#check @Total.stalkComparison_homotopyEquivalence
#check @Total.replacement_spec
@[stacks 0FKT] #check @exists_flasqueResolution

end AlgebraicGeometry.RingedSpace.Godement
