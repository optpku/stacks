module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ApproximationByPerfectComplexes
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Definition 75.14.2: approximation by perfect complexes on an algebraic space
means that every closed subset with quasi-compact open complement admits a
uniform shift for supported pseudo-coherent objects to have perfect approximations. -/
@[stacks 08HJ] #check
  (AlgebraicGeometry.AlgebraicSpace.HasApproximationByPerfectComplexes :
    {S : Scheme.{u}} → AlgebraicSpace S → Prop)

#check
  (AlgebraicGeometry.AlgebraicSpace.hasApproximationByPerfectComplexes_iff :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) →
      (HasApproximationByPerfectComplexes X ↔
        ∀ T : Closeds (Points X), QuasiCompact (OpenSubspace.ofOpensι T.compl) →
          ∃ r : ℤ,
            ∀ (E : DerivedQCoh X) (m : ℤ),
              IsMPseudoCoherent X E.obj (m - r) →
                (∀ i : ℤ, m - r ≤ i →
                  Modules.moduleSupportedOn (T : Set (Points X))
                    ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj)) →
                  HasPerfectApproximation T E m))

#check
  (AlgebraicGeometry.AlgebraicSpace.HasApproximationByPerfectComplexes.existsShift :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
      (hX : HasApproximationByPerfectComplexes X) → (T : Closeds (Points X)) →
      (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl)) →
      ∃ r : ℤ,
        ∀ (E : DerivedQCoh X) (m : ℤ),
          IsMPseudoCoherent X E.obj (m - r) →
            (∀ i : ℤ, m - r ≤ i →
              Modules.moduleSupportedOn (T : Set (Points X))
                ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj)) →
              HasPerfectApproximation T E m)

end AlgebraicGeometry.AlgebraicSpace
