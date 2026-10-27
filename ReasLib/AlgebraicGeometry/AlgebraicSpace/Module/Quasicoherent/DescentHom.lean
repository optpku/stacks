/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AtlasDescent

/-! # Descent of quasi-coherent morphisms along a scheme atlas -/

@[expose] public section

open CategoryTheory

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- Descend a morphism on a locally surjective étale scheme atlas that commutes with the
canonical actions on its kernel-pair groupoid by bundling it as an equivariant morphism
and taking its preimage under the full restriction-with-action functor. -/
def descHom (φ : ofOver U ⟶ X) [Etale φ]
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ]
    {F G : QCoh X}
    (f : (restrictToScheme U).obj ((pullback φ).obj F) ⟶
      (restrictToScheme U).obj ((pullback φ).obj G))
    (compatibility :
      (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).map f ≫ action φ G =
        action φ F ≫ (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).map f) : F ⟶ G :=
  (toGroupoid φ).preimage (GroupoidScheme.System.Hom.of f compatibility)

/-- Restriction of a descended compatible morphism is the specified atlas morphism. -/
theorem descHom_restrict (φ : ofOver U ⟶ X) [Etale φ]
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ]
    {F G : QCoh X}
    (f : (restrictToScheme U).obj ((pullback φ).obj F) ⟶
      (restrictToScheme U).obj ((pullback φ).obj G))
    (compatibility :
      (Scheme.QCoh.pullback (atlasGroupoid φ).t.left).map f ≫ action φ G =
        action φ F ≫ (Scheme.QCoh.pullback (atlasGroupoid φ).s.left).map f) :
    (restrictToScheme U).map ((pullback φ).map (descHom φ f compatibility)) = f := sorry

/-- A morphism of quasi-coherent modules is uniquely determined by its restriction to a
locally surjective étale scheme atlas. -/
theorem descHom_unique (φ : ofOver U ⟶ X) [Etale φ]
    [Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ]
    {F G : QCoh X} (a b : F ⟶ G)
    (h : (restrictToScheme U).map ((pullback φ).map a) =
      (restrictToScheme U).map ((pullback φ).map b)) : a = b := sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
