module

public import stacks_project.Chap75.Lemma_75_16_3_Compact
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory TopologicalSpace

universe u

/- Lemma 75.16.3 -/
@[stacks 0AED] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.isCompactObject_iff_isPerfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (T : Closeds (Points X)),
      QuasiCompact (OpenSubspace.ofOpensι T.compl) →
        ∀ (E : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn X (T : Set (Points X))),
          IsCompactObject E ↔ ModuleDerived.IsPerfect E.obj)
