/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Genus

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.9.4 (1): the parent locus decomposes into clopen genus loci. -/
@[stacks 0E6K]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_ofGenus_clopen_decomposition :
  ∀ {S : Scheme.{u}} (P : Obj S), h0Dim1 S P →
    ∃ U : ℕ → (base P).left.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun g g' ↦ Disjoint (U g : Set (base P).left) (U g')) ∧
          (∀ g, IsClopen (U g : Set (base P).left)) ∧
            ∀ g, ∀ {Q : Obj S} (φ : Q ⟶ P),
              ofGenus g S Q ↔ Set.range (baseMap φ).left ⊆ U g)

/- Lemma 109.9.4 (2): the family characterization of the genus locus. -/
@[stacks 0E6K]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.ofGenus_iff :
  ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    ofGenus g S P ↔
      (∀ {Z : AlgebraicSpace S} (φ : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) φ))) ∧
        (∀ y : Points (ofOver (base P)), fiberDimension (hom P) y = 1) ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank g
            (higherDirectImageOne (hom P)))

/- Lemma 109.9.4 (3): the proper-field characterization of the genus locus. -/
@[stacks 0E6K]
#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.ofGenus_iff_scheme :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ),
    ofGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      ∃ (hdim1 : topologicalKrullDim X.left = 1)
        (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
        SchemeOverField.genus X hdim1 hΓ = g)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
