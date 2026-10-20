/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Projective
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper

universe u

/- Lemma 31.30.4: For a relative projective-spectrum presentation whose degree-zero
algebras are finite over the base, finite type over degree zero is equivalent to finite type
over the base. Under these conditions the structural morphism is locally projective and hence
proper. -/
@[stacks 0800] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation.finiteTypeConditions_iff :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p),
      (P.FiniteDegreeZeroAlgebra ∧ P.FiniteTypeAsDegreeZeroAlgebra) ↔
        (P.FiniteDegreeZeroAlgebra ∧ P.FiniteTypeAsBaseAlgebra))

#check
  (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation.FiniteDegreeZeroAlgebra.locallyProjective :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      {P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p},
      P.FiniteDegreeZeroAlgebra → P.FiniteTypeAsDegreeZeroAlgebra →
        AlgebraicGeometry.LocallyProjective p)

#check
  (AlgebraicGeometry.LocallyProjective.isProper :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyProjective f], AlgebraicGeometry.IsProper f)
