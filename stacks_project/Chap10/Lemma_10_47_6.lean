/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine.Irreducible
public import ReasLib.Algebra.Category.CommAlgCat.FilteredColimit.FinitelyGenerated
import StacksCheckRecall

@[expose] public section

/-!
# Closure Properties of Geometrically Irreducible Affine Algebras

Lemma 10.47.6 is a canonical recall.  The reusable owner is the affine
geometric-irreducibility API in `AlgebraicGeometry.SchemeOverField`: it is
stated first for injective maps, then for finitely generated subalgebras and
filtered-or-empty colimits.  The latter categorical form subsumes the source
ordered directed-system formulation without choosing a presentation of the
index category.

@stack 037N
-/

/- Lemma 10.47.6 (1) (Tag 037N): geometric irreducibility descends along an
injective morphism of affine algebras, hence along a subalgebra inclusion. -/
@[stacks 037N]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.of_injective
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.of_subalgebra
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.instSubalgebra

/- Lemma 10.47.6 (2) (Tag 037N): it is enough to test geometric irreducibility
on finitely generated subalgebras. -/
@[stacks 037N]
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.of_forall_fg

/- Lemma 10.47.6 (3) (Tag 037N): filtered-or-empty colimits preserve geometric
irreducibility. -/
@[stacks 037N]
#check @CommAlgCat.exists_fg_subalgebra_factorization
#check @CommAlgCat.exists_injective_stage_of_fg_subalgebra_colimit
#check @AlgebraicGeometry.SchemeOverField.GeometricallyIrreducible.of_filteredColimit
