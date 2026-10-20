/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalSpectrum.CompletionAlong

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace
open AlgebraicGeometry.AffineFormalAlgebraicSpace

universe u

/- Lemma 87.33.4: An adic morphism from the formal spectrum of a complete local
Noetherian `S`-algebra to the completion along a closed subset with quasi-compact
open complement corresponds to a unique morphism from its spectrum whose
inverse image of the subset is the closed point. -/
@[stacks 0GBU] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.existsUnique_specHom_of_adicSpfHom :
    ∀ {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    [TopologicalRing.IsWeaklyAdmissibleRing R]
    (h_adic : IsAdic (maximalIdeal R)) {S : Scheme.{u}}
    (structureHom : Spec (.of R) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (X : AlgebraicSpace S) (T : Closeds (Points X))
    [AlgebraicSpace.QuasiCompact (OpenSubspace.Construction.ι X T.compl)]
    (p : spf R structureHom ⟶
      (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).obj
        (completionAlong X T))
    (hp : AlgebraicSpace.representableByAlgebraicSpaces
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map p)),
    ∃! g : ofOver (Over.mk structureHom) ⟶ X,
      Points.mapOfOver g ⁻¹' (T : Set (Points X)) = {closedPoint R} ∧
        specHomToSpfHom_algebraicSpace structureHom X g =
          p ≫ (presheafToSheaf (Scheme.fppfTopology.over S) (Type u)).map
            (completionAlong.ι X T))
