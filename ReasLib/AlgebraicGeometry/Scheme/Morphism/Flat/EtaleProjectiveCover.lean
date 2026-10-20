/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleProjectiveCover
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finitely presented scheme morphism flat at every point of a fibre admits an affine
elementary étale base neighbourhood and an affine étale source covering that fibre whose
global sections are projective over those of the refined base. -/
theorem existsAffineEtaleCoverWithProjectiveSections {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FinitePresentation f] (s : S)
    (h_flat : ∀ x : f.fiber s, f.flatAt (f.fiberι s x)) :
    ∃ V : EtaleNeighborhood.Elementary S s,
      let S' := V.obj
      ∃ _ : IsAffine S'.toEtale.left,
        ∃ X' : X.Etale,
          ∃ _ : IsAffine X'.left,
            ∃ f' : X'.left ⟶ S'.toEtale.left,
              CommSq X'.hom f' f S'.toEtale.hom ∧
                Set.range (f.fiberι s) ⊆ Set.range X'.hom ∧
                  Module.Projective Γ(S'.toEtale.left, ⊤)
                    (Scheme.Hom.sectionsMod f' ⊤ ⊤ le_top (𝟙_ X'.left.Modules)) := sorry

end AlgebraicGeometry.Scheme.Hom
