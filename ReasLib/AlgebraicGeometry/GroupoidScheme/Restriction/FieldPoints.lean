/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.IsAlgClosed.Embeddings
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Field
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.RationalPoint

/-!
# Field-valued points of restricted groupoid schemes

This module lifts arrow points of a groupoid scheme after restriction to an algebraically closed
field extension.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

open Scheme.Hom.ResidueField

/-- Every arrow point of a groupoid scheme whose object scheme is the spectrum of a field lifts
after restriction to an algebraically closed field extension, with both endpoints inducing
isomorphisms on residue fields. -/
theorem existsAlgebraicallyClosedArrowLift
    {S : Scheme.{u}} (G : GroupoidScheme S) {k : Type u} [Field k]
    (eU : Spec (CommRingCat.of k) ≅ G.U.left) (r : G.R.left) :
    ∃ (K : Type u) (_ : Field K) (ι : k →+* K) (_ : IsAlgClosed K),
      let g := G.fieldRestriction eU ι
      let G' := G.pullback g
      let φ := G.pullbackHom g
      ∃ r' : G'.R.left,
        φ.arrow.left r' = r ∧
          IsIso (CommRingCat.ofHom (mapOfSpec G'.s.left r')) ∧
          IsIso (CommRingCat.ofHom (mapOfSpec G'.t.left r')) := sorry

end AlgebraicGeometry.GroupoidScheme
