/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplexCategory.Pointlike
public import ReasLib.AlgebraicTopology.SimplicialObject.Flat
public import ReasLib.AlgebraicTopology.SimplicialObject.Tensor.EilenbergZilber
import StacksCheckRecall

/-!
# Remark 21.39.11 (Simplicial modules)

The reusable pointlike-simplex and Eilenberg-Zilber statements live in ReasLib.  This file records
their source-facing specialization to termwise-flat simplicial modules.
-/

@[expose] public section

open CategoryTheory
open scoped DoldKan Simplicial

universe u

namespace AlgebraicTopology.AlternatingFaceMapComplex

/- Remark 21.39.11 (Simplicial modules): the identity cosimplicial object on `SimplexCategory`
has pointlike Hom spaces because its Hom simplicial sets are standard simplices.  For a
commutative ring `R` and termwise-flat simplicial `R`-modules `X` and `Y`, the alternating-face
complex `K[X ⊗ Y]` is quasi-isomorphic to the total tensor complex `K[X] ⊗ K[Y]`.  The canonical
Eilenberg-Zilber owner is stronger: its comparison does not require flatness. -/
@[stacks 08QD "Remark 21.39.11 termwise-flat Eilenberg-Zilber comparison"]
#check @ModuleCat.exists_quasiIso_of_termwiseFlat

@[stacks 08QD "Remark 21.39.11 Eilenberg-Zilber comparison"]
#check @ModuleCat.tensorComparison.quasiIso

@[stacks 08QD "Remark 21.39.11 identity simplex-category Hom spaces"]
#check SimplexCategory.identity_hasHomSpaces

@[stacks 08QD "Remark 21.39.11 simplicial module flatness bridge"]
#check @CategoryTheory.SimplicialObject.isTermwiseFlat_iff_moduleFlat

end AlgebraicTopology.AlternatingFaceMapComplex
