module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.ExactSequence

universe u

/- Lemma 31.2.4 (1): in a short exact sequence of quasi-coherent modules on a scheme, the
associated points of the middle term lie in the union of those of the outer terms. -/
@[stacks 05AE] #check
  (AlgebraicGeometry.Scheme.Modules.associatedPoints_middle_subset_union_of_shortExact :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {S : CategoryTheory.ShortComplex X.Modules}
      [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent],
      S.ShortExact →
        AlgebraicGeometry.Scheme.Modules.associatedPoints S.X₂ ⊆
          AlgebraicGeometry.Scheme.Modules.associatedPoints S.X₁ ∪
            AlgebraicGeometry.Scheme.Modules.associatedPoints S.X₃)

/- Lemma 31.2.4 (2): in a short exact sequence of quasi-coherent modules on a scheme, the
associated points of the left term are associated points of the middle term. -/
@[stacks 05AE] #check
  (AlgebraicGeometry.Scheme.Modules.associatedPoints_left_subset_of_shortExact :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {S : CategoryTheory.ShortComplex X.Modules}
      [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent],
      S.ShortExact →
        AlgebraicGeometry.Scheme.Modules.associatedPoints S.X₁ ⊆
          AlgebraicGeometry.Scheme.Modules.associatedPoints S.X₂)
