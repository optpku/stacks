/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Morita

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/- Remark 36.18.3 (Variant with support): for a quasi-compact quasi-separated scheme `X`
and a closed subset `T` with quasi-compact complement, there is an integral cochain
differential graded algebra whose cohomology is nonzero in only finitely many degrees and
whose derived category is linearly triangulated equivalent to `D_QCoh,T(𝒪_X)`. -/
@[stacks 0DJL] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.exists_dgAlgebra_equivalence :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (T : TopologicalSpace.Closeds X) (hT : IsCompact (T.compl : Set X)),
      ∃ E : CochainDGAlgebra.{0, u} ℤ,
        Set.Finite {i : ℤ | ¬ IsZero (E.homology i)} ∧
          Nonempty (RLinear.TriangulatedEquivalence ℤ
            (DifferentialGradedModule.Derived.Category.{0, u} E)
            (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn X T)))
