/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Morita

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Theorem 36.18.2: for a quasi-compact quasi-separated scheme `X`, there is an integral
cochain differential graded algebra whose homology is nonzero in only finitely many degrees
and whose derived category is linearly triangulated equivalent to `D_QCoh(𝒪_X)`. -/
@[stacks 09M5] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_dgAlgebra_equivalence :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X],
      ∃ E : CochainDGAlgebra.{0, u} ℤ,
        Set.Finite {i : ℤ | ¬ IsZero (E.homology i)} ∧
          Nonempty (RLinear.TriangulatedEquivalence ℤ
            (DifferentialGradedModule.Derived.Category.{0, u} E)
            (AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)))
