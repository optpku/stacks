/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stalk

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 40.10.8 (1): every local ring of the arrow scheme has a unique minimal prime ideal. -/
@[stacks 04LT] #check
  (AlgebraicGeometry.GroupoidScheme.existsUniqueMinimalPrime_stalk :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {k : Type u} [Field k] (uIso : G.U.left ≅ Spec (CommRingCat.of k))
      (r : G.R.left),
      let R := G.R.left
      ∃! p : Ideal (R.presheaf.stalk r),
        p ∈ minimalPrimes (R.presheaf.stalk r))

/- Lemma 40.10.8 (2): exactly one irreducible component of the arrow scheme contains the
identity point. -/
@[stacks 04LT] #check
  (AlgebraicGeometry.GroupoidScheme.existsUniqueIrreducibleComponent_throughIdentity :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {k : Type u} [Field k] (uIso : G.U.left ≅ Spec (CommRingCat.of k)),
      ∃! Z : irreducibleComponents G.R.left,
        G.e.left (uIso.inv (IsLocalRing.closedPoint k)) ∈ (Z : Set G.R.left))

/- Lemma 40.10.8 (3): every irreducible component containing the identity point is
geometrically irreducible for the field structure induced by the source map. -/
@[stacks 04LT] #check
  (AlgebraicGeometry.GroupoidScheme.geometricallyIrreducible_identityIrreducibleComponentSource :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {k : Type u} [Field k] (uIso : G.U.left ≅ Spec (CommRingCat.of k))
      (Z : irreducibleComponents G.R.left)
      (hZ : G.e.left (uIso.inv (IsLocalRing.closedPoint k)) ∈ (Z : Set G.R.left)),
      AlgebraicGeometry.GeometricallyIrreducible
        (irreducibleComponentSubschemeι G.R.left Z ≫ G.s.left ≫ uIso.hom))

/- Lemma 40.10.8 (4): every irreducible component containing the identity point is
geometrically irreducible for the field structure induced by the target map. -/
@[stacks 04LT] #check
  (AlgebraicGeometry.GroupoidScheme.geometricallyIrreducible_identityIrreducibleComponentTarget :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {k : Type u} [Field k] (uIso : G.U.left ≅ Spec (CommRingCat.of k))
      (Z : irreducibleComponents G.R.left)
      (hZ : G.e.left (uIso.inv (IsLocalRing.closedPoint k)) ∈ (Z : Set G.R.left)),
      AlgebraicGeometry.GeometricallyIrreducible
        (irreducibleComponentSubschemeι G.R.left Z ≫ G.t.left ≫ uIso.hom))
