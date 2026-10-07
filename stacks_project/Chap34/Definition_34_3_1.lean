module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Zariski
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 34.3.1: a Zariski covering of a scheme is a family of open immersions whose
ranges cover the target scheme. -/
@[stacks 020O] #check
  (AlgebraicGeometry.Scheme.ofArrows_mem_zariskiPrecoverage_iff :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {I : Type v}
      (X : I → AlgebraicGeometry.Scheme.{u}) (f : ∀ i, X i ⟶ T),
      CategoryTheory.Presieve.ofArrows X f ∈
          AlgebraicGeometry.Scheme.zariskiPrecoverage T ↔
        (∀ i, AlgebraicGeometry.IsOpenImmersion (f i)) ∧
          (⋃ i, Set.range (f i)) = Set.univ)

/- The canonical bundled representation of a Zariski cover of a scheme. -/
#check AlgebraicGeometry.Scheme.OpenCover

/- The ranges of the members of a bundled scheme open cover form a topological open cover. -/
#check AlgebraicGeometry.Scheme.OpenCover.isOpenCover_opensRange
