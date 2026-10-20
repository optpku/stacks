/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry RelativeDerivation

universe u

namespace AlgebraicGeometry

/- Lemma 53.20.1: a scheme morphism is flat and locally of finite presentation, with
every nonempty fibre equidimensional of dimension one and at worst nodal, if and only if it
is syntomic of relative dimension one and its first-Fitting singular subscheme is unramified
over the base. -/
@[stacks 0C59] #check
  (AlgebraicGeometry.fibersAtWorstNodal_iff_syntomicAndSingularUnramified :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    ((Flat f ∧ LocallyOfFinitePresentation f) ∧
        Scheme.Hom.RelativeDimension f 1 ∧
          ∀ s : S,
            SchemeOverField.atWorstNodal (Over.mk (f.fiberOverSpecResidueField s).hom)) ↔
      SyntomicOfRelativeDimension f 1 ∧
        Unramified ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) 1).subschemeι ≫ f))

end AlgebraicGeometry
