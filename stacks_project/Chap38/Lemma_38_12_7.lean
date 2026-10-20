/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.EtaleProjectiveCover

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 38.12.7: a finitely presented scheme morphism flat at every point of a fibre
admits an affine elementary étale base neighbourhood and an affine étale source cover
of that fibre whose global sections are projective over those of the refined base. -/
@[stacks 05KX] #check
  (AlgebraicGeometry.Scheme.Hom.existsAffineEtaleCoverWithProjectiveSections :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation f] (s : S),
      (∀ x : f.fiber s, f.flatAt (f.fiberι s x)) →
        ∃ V : AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary S s,
          let S' := V.obj
          ∃ _ : AlgebraicGeometry.IsAffine S'.toEtale.left,
            ∃ X' : X.Etale,
              ∃ _ : AlgebraicGeometry.IsAffine X'.left,
                ∃ f' : X'.left ⟶ S'.toEtale.left,
                  CommSq X'.hom f' f S'.toEtale.hom ∧
                    Set.range (f.fiberι s) ⊆ Set.range X'.hom ∧
                      Module.Projective Γ(S'.toEtale.left, ⊤)
                        (AlgebraicGeometry.Scheme.Hom.sectionsMod f' ⊤ ⊤ le_top
                          (𝟙_ X'.left.Modules)))
