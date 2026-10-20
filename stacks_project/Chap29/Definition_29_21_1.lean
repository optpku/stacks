/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/- Definition 29.21.1: a morphism is of finite presentation at a source point when there are
affine source and target neighborhoods for which the induced ring homomorphism is of finite
presentation. It is locally of finite presentation when this holds at every source point, and it
is of finite presentation when it is also quasi-compact and quasi-separated. -/
@[stacks 01TP] #check
  (AlgebraicGeometry.Scheme.Hom.finitePresentationAt_iff f x :
    AlgebraicGeometry.Scheme.Hom.FinitePresentationAt f x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ V : S.affineOpens,
          ∃ e : U ≤ f ⁻¹ᵁ V,
            (CommRingCat.Hom.hom (f.appLE V U e)).FinitePresentation)

#check
  (AlgebraicGeometry.Scheme.Hom.locallyOfFinitePresentation_iff_forall_finitePresentationAt f :
    LocallyOfFinitePresentation f ↔
      ∀ x : X, AlgebraicGeometry.Scheme.Hom.FinitePresentationAt f x)

#check
  (AlgebraicGeometry.Scheme.Hom.finitePresentation_iff f :
    AlgebraicGeometry.Scheme.Hom.FinitePresentation f ↔
      LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f)

end AlgebraicGeometry
