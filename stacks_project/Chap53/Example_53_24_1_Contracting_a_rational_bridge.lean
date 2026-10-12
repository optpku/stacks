/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge.Contraction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

@[expose] public section

/- Example 53.24.1 (Contracting a rational bridge): a proper one-dimensional nodal scheme with
constant global functions admits a contraction of every rational bridge, preserving the
curve invariants, the structure sheaf, first higher direct image, and genus. -/
@[stacks 0E3M] #check (AlgebraicGeometry.RationalBridge.existsContraction :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : SchemeOverField.atWorstNodal X)
    (B : RationalBridge X),
    ∃ (Y : SchemeOverField k) (c : X ⟶ Y)
      (a : (RationalBridge.complementScheme X B.component).left ⟶ Y.left)
      (b : Spec (Scheme.globalSectionsRing
        (RationalBridge.componentScheme X B.component).left) ⟶ Y.left)
      (componentMap : (RationalBridge.componentScheme X B.component).left ⟶ Y.left)
      (componentToSpec : (RationalBridge.componentScheme X B.component).left ⟶
        Spec (Scheme.globalSectionsRing
          (RationalBridge.componentScheme X B.component).left))
      (intersectionToSpec : (RationalBridge.intersectionScheme X B.component).left ⟶
        Spec (Scheme.globalSectionsRing
          (RationalBridge.componentScheme X B.component).left)),
      B.IsContraction Y c a b componentMap componentToSpec intersectionToSpec)
