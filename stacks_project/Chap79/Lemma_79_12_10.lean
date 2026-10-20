/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.Atlas
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocallySurjective
import StacksCheckRecall

/-!
# Étale atlas of the finite-part functor
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/- Lemma 79.12.10: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is separated and locally quasi-finite, then
there exists a scheme `U` étale over `Y` and a surjective étale morphism
`U ⟶ (X/Y)_fin` over `Y`. -/
@[stacks 04QG] #check (AlgebraicGeometry.AlgebraicSpace.FinitePart.exists_surjective_etale :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicSpace.Separated f] [AlgebraicSpace.LocallyQuasiFinite f],
    ∃ (U : Over S) (a : ofOver U ⟶ Y) (φ : yoneda.obj U ⟶ functor f),
      AlgebraicSpace.Etale a ∧ φ ≫ hom f = a ∧
        (over (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).presheaf φ ∧
        (over (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})).presheaf φ)

/- A representably étale and surjective morphism of presheaves is
étale-locally surjective. -/
#check (AlgebraicGeometry.Scheme.isLocallySurjective_of_surjective_etale :
    ∀ {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {φ : F ⟶ G},
      (over (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).presheaf φ →
      (over (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})).presheaf φ →
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) φ)

end AlgebraicGeometry.AlgebraicSpace.FinitePart
