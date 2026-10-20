/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Acyclic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

/- Lemma 20.37.10 (0BKT): let `(X, 𝒪_X)` be a ringed space, let `K ∈ D(𝒪_X)`, and let `ℬ`
be a basis of opens of `X`. If `H^p(U, H^q(K)) = 0` for every `U ∈ ℬ`, every `q : ℤ`, and
every `p > 0`, then for every `U ∈ ℬ` and every `q : ℤ`, the hypercohomology group `H^q(U, K)`
is canonically isomorphic to `H^0(U, H^q(K))`. -/
@[stacks 0BKT "hypercohomology from acyclic cohomology sheaves"]
#check @Basis.zeroDegreeIsoOfSheaves

@[stacks 0BKT "basiswise acyclicity in a fixed degree"]
#check @Basis.AcyclicIn
@[stacks 0BKT "basiswise acyclicity"]
#check @Basis.Acyclic
@[stacks 0BKT "basiswise sheaf acyclicity in a fixed degree"]
#check @Basis.SheafAcyclicIn
@[stacks 0BKT "basiswise sheaf acyclicity"]
#check @Basis.SheafAcyclic
@[stacks 0BKT "basiswise acyclicity degree projection"]
#check @Basis.Acyclic.inDegree
@[stacks 0BKT "basiswise sheaf acyclicity degree projection"]
#check @Basis.SheafAcyclic.inDegree
@[stacks 0BKT "basiswise acyclicity equivalence"]
#check @Basis.acyclicIn_iff_sheafAcyclicIn
@[stacks 0BKT "basiswise sheaf acyclicity equivalence"]
#check @Basis.acyclic_iff_sheafAcyclic
@[stacks 0BKT "zero-degree hypercohomology comparison"]
#check @Basis.zeroDegreeIso
@[stacks 0BKT "zero-degree comparison for a sheaf"]
#check @Basis.zeroDegreeIsoOfSheaf

end
