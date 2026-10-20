/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.FieldPoints
public import stacks_project.Chap40.«40_3_0_2_Comparison»

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Groupoid

open Scheme.Hom.ResidueField

/-- For a morphism to the spectrum of a field, applying `Spec.map` to the canonical residue-field
map recovers the morphism from the residue-field spectrum followed by the original morphism. -/
theorem SpecMap_mapOfSpec {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    Spec.map (CommRingCat.ofHom (mapOfSpec f x)) = X.fromSpecResidueField x ≫ f := by
  exact AlgebraicGeometry.Scheme.Hom.ResidueField.specMap_mapOfSpec f x

/-- Every arrow of a diagrammatic groupoid over a field lifts after restriction to an
algebraically closed field extension, with both endpoints inducing residue-field isomorphisms. -/
theorem existsAlgebraicallyClosedArrowLift
    {S : Scheme.{u}} (G : Groupoid S) {k : Type u} [Field k]
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) (r : G.R.left) :
    ∃ (K : Type u) (_ : Field K) (ι : k →+* K) (_ : IsAlgClosed K),
      let g := G.toGroupoidScheme.fieldRestriction eU ι
      let G' := G.toGroupoidScheme.pullback g
      let φ := G.toGroupoidScheme.pullbackHom g
      ∃ r' : G'.R.left,
        φ.arrow.left r' = r ∧
          IsIso (CommRingCat.ofHom (mapOfSpec G'.s.left r')) ∧
          IsIso (CommRingCat.ofHom (mapOfSpec G'.t.left r')) := by
  exact AlgebraicGeometry.GroupoidScheme.existsAlgebraicallyClosedArrowLift
    G.toGroupoidScheme eU r

end AlgebraicGeometry.Scheme.Groupoid

/-
Lemma 40.10.5: every arrow point of a groupoid scheme over the spectrum of a field lifts after
restriction to an algebraically closed field extension, with both endpoint residue-field maps
isomorphisms.
-/
@[stacks 04LR] #check
  (AlgebraicGeometry.GroupoidScheme.existsAlgebraicallyClosedArrowLift :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {k : Type u} [Field k]
      (eU : Spec (CommRingCat.of k) ≅ G.U.left) (r : G.R.left),
      ∃ (K : Type u) (_ : Field K) (ι : k →+* K) (_ : IsAlgClosed K),
        let g := G.fieldRestriction eU ι
        let G' := G.pullback g
        let φ := G.pullbackHom g
        ∃ r' : G'.R.left,
          φ.arrow.left r' = r ∧
            IsIso (CommRingCat.ofHom
              (AlgebraicGeometry.Scheme.Hom.ResidueField.mapOfSpec G'.s.left r')) ∧
            IsIso (CommRingCat.ofHom
              (AlgebraicGeometry.Scheme.Hom.ResidueField.mapOfSpec G'.t.left r')))
