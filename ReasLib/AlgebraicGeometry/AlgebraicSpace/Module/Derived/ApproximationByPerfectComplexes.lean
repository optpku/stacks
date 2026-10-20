module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PerfectApproximation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent

/-!
# Approximation by perfect complexes on algebraic spaces

Approximation by perfect complexes holds on an algebraic space when every closed
subset whose open-complement immersion is quasi-compact admits a uniform integer
after which supported pseudo-coherent objects of `DerivedQCoh` have perfect
approximations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Approximation by perfect complexes holds on an algebraic space if every closed
subset whose open-complement immersion is quasi-compact admits a uniform integer
`r` after which every `(m - r)`-pseudo-coherent object of `DerivedQCoh` whose
cohomology in degrees at least `m - r` is supported on that closed subset has a
perfect approximation. -/
def HasApproximationByPerfectComplexes {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∀ T : Closeds (Points X), QuasiCompact ((OpenSubspace.fromOpens T.compl).ι) →
    ∃ r : ℤ,
      ∀ (E : DerivedQCoh X) (m : ℤ),
        IsMPseudoCoherent X E.obj (m - r) →
          (∀ i : ℤ, m - r ≤ i →
            Modules.moduleSupportedOn (T : Set (Points X))
              ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj)) →
            HasPerfectApproximation T E m

/-- Approximation by perfect complexes is the nested quantification over
quasi-compact complement immersions, a uniform shift, `(m - r)`-pseudo-coherence,
degreewise support, and perfect approximation. -/
theorem hasApproximationByPerfectComplexes_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasApproximationByPerfectComplexes X ↔
      ∀ T : Closeds (Points X), QuasiCompact ((OpenSubspace.fromOpens T.compl).ι) →
        ∃ r : ℤ,
          ∀ (E : DerivedQCoh X) (m : ℤ),
            IsMPseudoCoherent X E.obj (m - r) →
              (∀ i : ℤ, m - r ≤ i →
                Modules.moduleSupportedOn (T : Set (Points X))
                  ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj)) →
                HasPerfectApproximation T E m := sorry

namespace HasApproximationByPerfectComplexes

/-- Approximation by perfect complexes supplies a uniform pseudo-coherence shift for each
closed subset whose open-complement immersion is quasi-compact. -/
theorem existsShift {S : Scheme.{u}} {X : AlgebraicSpace S}
    (hX : HasApproximationByPerfectComplexes X) (T : Closeds (Points X))
    (hT : QuasiCompact ((OpenSubspace.fromOpens T.compl).ι)) :
    ∃ r : ℤ,
      ∀ (E : DerivedQCoh X) (m : ℤ),
        IsMPseudoCoherent X E.obj (m - r) →
          (∀ i : ℤ, m - r ≤ i →
            Modules.moduleSupportedOn (T : Set (Points X))
              ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj)) →
            HasPerfectApproximation T E m := sorry

end HasApproximationByPerfectComplexes

end AlgebraicGeometry.AlgebraicSpace
