/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge.DualizingModule

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RationalBridge

/- Lemma 53.24.4 -/
@[stacks 0E3N] #check (AlgebraicGeometry.RationalBridge.curveDualizingModule_pullback_isomorphic :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (h_dimension : topologicalKrullDim X.left = 1)
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (h_nodal : SchemeOverField.atWorstNodal X)
      (B : RationalBridge X) (Y : SchemeOverField k) (c : X ⟶ Y)
      (a : (complementScheme X B.component).left ⟶ Y.left)
      (b : Spec (Scheme.globalSectionsRing (componentScheme X B.component).left) ⟶ Y.left)
      (componentMap : (componentScheme X B.component).left ⟶ Y.left)
      (componentToSpec : (componentScheme X B.component).left ⟶
        Spec (Scheme.globalSectionsRing (componentScheme X B.component).left))
      (intersectionToSpec : (intersectionScheme X B.component).left ⟶
        Spec (Scheme.globalSectionsRing (componentScheme X B.component).left))
      (h_contraction :
        B.IsContraction Y c a b componentMap componentToSpec intersectionToSpec),
      IsIsomorphic
        ((Scheme.Modules.pullback c.left).obj
          (@curveDualizingModule k _ Y.left Y.hom h_contraction.target_proper))
        (curveDualizingModule X.hom))

end AlgebraicGeometry.RationalBridge
