/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.GeometricallyReducedConnected

/-!
# Geometrically reduced and connected curves of dimension 1

There is an open substack `𝒞urves^{grc, 1} ⊂ 𝒞urves` classifying families of
curves with reduced, connected geometric fibres of dimension `1`, equivalently
proper geometrically reduced geometrically connected schemes of dimension `1`
over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/- Lemma 109.11.1. There is an open substack of curves classifying families
with reduced, connected geometric fibres of dimension one, with the following
family and field-valued characterizations. -/
@[stacks 0E1I] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_geometricallyReducedConnectedDim1_open :
    ∀ {S : Scheme.{u}} (P : Obj S),
      ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
        geometricallyReducedConnectedDim1 S Q ↔ Set.range (baseMap φ).left ⊆ U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReducedConnectedDim1_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
      geometricallyReducedConnectedDim1 S P ↔
        Hom.HasReducedGeometricFibres (hom P) ∧
          AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres (hom P) ∧
            ∀ ybar : GeometricPoint (ofOver (base P)),
              dimension (fieldFiber (hom P) ybar.toFieldValuedPoint) = 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_geometricallyReducedConnectedDim1_iff_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      geometricallyReducedConnectedDim1 (Spec (CommRingCat.of k))
          (mkOfSchemeOverField X hdim) ↔
        SchemeOverField.geometricallyReduced X ∧
          GeometricallyConnected X.hom ∧ topologicalKrullDim X.left = 1)

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace

