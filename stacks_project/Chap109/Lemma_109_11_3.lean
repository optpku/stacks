/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Restrict
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.GeometricallyReducedConnected.Genus

/-!
# Geometrically reduced and connected curves of a given genus
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.11.3 (1): The geometrically reduced connected dimension-one locus
decomposes into clopen genus loci under every cartesian morphism of families. -/
@[stacks 0E1K] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_geometricallyReducedConnectedDim1OfGenus_clopen_decomposition :
    ∀ {S : Scheme.{u}} (P : Obj S) (h : geometricallyReducedConnectedDim1 S P),
    ∃ U : ℕ → (base P).left.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun g g' ↦ Disjoint (U g : Set (base P).left) (U g')) ∧
          (∀ g, IsClopen (U g : Set (base P).left)) ∧
            ∀ g, ∀ {Q : Obj S} (φ : Q ⟶ P),
              geometricallyReducedConnectedDim1OfGenus g S Q ↔
                Set.range (baseMap φ).left ⊆ U g)

/- Lemma 109.11.3 (2): Membership is characterized by reduced, connected geometric
fibres of dimension one and a first higher direct image locally free of rank g. -/
@[stacks 0E1K] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReducedConnectedDim1OfGenus_iff_geometricFibres :
    ∀ {S : Scheme.{u}} (P : Obj S) (g : ℕ),
    geometricallyReducedConnectedDim1OfGenus g S P ↔
      Hom.HasReducedGeometricFibres (hom P) ∧
        AlgebraicGeometry.AlgebraicSpace.HasConnectedGeometricFibres (hom P) ∧
          (∀ ybar : GeometricPoint (ofOver (base P)),
              dimension (fieldFiber (hom P) ybar.toFieldValuedPoint) = 1) ∧
            SheafOfModules.IsFiniteLocallyFreeOfRank g
              (higherDirectImageOne (hom P)))

/- Lemma 109.11.3 (3): For a proper scheme of dimension at most one over a field,
membership is characterized by geometric reducedness, geometric connectedness,
dimension one, and genus g. -/
@[stacks 0E1K] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReducedConnectedDim1OfGenus_iff_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ),
    geometricallyReducedConnectedDim1OfGenus g (Spec (CommRingCat.of k))
        (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.geometricallyReduced X ∧
        GeometricallyConnected X.hom ∧
          ∃ (hdim1 : topologicalKrullDim X.left = 1)
            (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
            SchemeOverField.genus X hdim1 hΓ = g)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
