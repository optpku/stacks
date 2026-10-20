/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleProjective
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Cofiltered
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import Mathlib.AlgebraicGeometry.Fiber

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finitely presented module that is flat at every point of a fibre admits an affine
elementary étale base neighbourhood and an affine étale source covering the fibre, with
projective pulled-back global sections over the refined base. -/
theorem existsAffineEtaleCoverWithProjectiveSections {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FinitePresentation f] (F : X.Modules) [F.IsFinitePresentation] (s : S)
    (h_flat : ∀ x : f.fiber s, flatOverAt F f (f.fiberι s x)) :
    ∃ V : EtaleNeighborhood.Elementary S s,
      let S' := V.obj
      ∃ _ : IsAffine S'.toEtale.left,
        ∃ X' : X.Etale,
          let F' := (Scheme.Modules.pullback X'.hom).obj F
          ∃ _ : IsAffine X'.left,
            ∃ f' : X'.left ⟶ S'.toEtale.left,
              CommSq X'.hom f' f S'.toEtale.hom ∧
                Set.range (f.fiberι s) ⊆ Set.range X'.hom ∧
                  Module.Projective Γ(S'.toEtale.left, ⊤)
                    (Scheme.Hom.sectionsMod f' ⊤ ⊤ le_top F') := sorry

end AlgebraicGeometry.Scheme.Modules
