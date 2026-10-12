/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleProjectiveCover
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.12.5: a finitely presented scheme morphism and finitely presented module
sheaf, flat at every point of a fibre, admit an affine elementary étale base neighbourhood
and an affine étale source cover of that fibre with projective pulled-back global sections. -/
@[stacks 05KW] #check
  (AlgebraicGeometry.Scheme.Modules.existsAffineEtaleCoverWithProjectiveSections :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
      (F : X.Modules) [F.IsFinitePresentation] (s : S)
      (h_flat : ∀ x : f.fiber s,
        AlgebraicGeometry.Scheme.Modules.flatOverAt F f (f.fiberι s x)),
      ∃ V : EtaleNeighborhood.Elementary S s,
        let S' := V.obj
        ∃ _ : IsAffine S'.toEtale.left,
          ∃ X' : X.Etale,
            let F' := (AlgebraicGeometry.Scheme.Modules.pullback X'.hom).obj F
            ∃ _ : IsAffine X'.left,
              ∃ f' : X'.left ⟶ S'.toEtale.left,
                CommSq X'.hom f' f S'.toEtale.hom ∧
                  Set.range (f.fiberι s) ⊆ Set.range X'.hom ∧
                    Module.Projective Γ(S'.toEtale.left, ⊤)
                      (Scheme.Hom.sectionsMod f' ⊤ ⊤ le_top F'))

end AlgebraicGeometry.Scheme.Modules
