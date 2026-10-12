/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleProjectiveOpen
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.19.3: a finitely presented module flat at a point over a locally finitely
presented morphism has projective sections on an affine neighborhood of the corresponding
point after an affine elementary étale base refinement. -/
@[stacks 05ME] #check
  (AlgebraicGeometry.Scheme.Modules.existsAffineOpenWithProjectiveSections :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
      (F : X.Modules) [F.IsFinitePresentation] (x : X) (h_flat : flatOverAt F f x),
      ∃ V : EtaleNeighborhood.Elementary S (f x),
        let S' := V.obj
        ∃ _ : IsAffine S'.toEtale.left,
          let X' := Limits.pullback f S'.toEtale.hom
          let p := Limits.pullback.snd f S'.toEtale.hom
          let F' := baseChangeModule f S'.toEtale.hom F
          ∃ x' : X',
            Limits.pullback.fst f S'.toEtale.hom x' = x ∧
              p x' = S'.point ∧
                ∃ U : X'.Opens, x' ∈ U ∧ IsAffineOpen U ∧
                  let M : ModuleCat Γ(S'.toEtale.left, ⊤) :=
                    Scheme.Hom.sectionsMod (U.ι ≫ p) ⊤ ⊤ le_top (F'.restrict U.ι)
                  Module.Projective Γ(S'.toEtale.left, ⊤) M)

end AlgebraicGeometry.Scheme.Modules
