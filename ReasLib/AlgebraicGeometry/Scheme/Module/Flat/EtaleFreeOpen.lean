/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleProjectiveOpen
public import ReasLib.Algebra.Module.Projective.LocalRing

/-!
# Free sections after elementary étale localization

This module records affine-local freeness after passing to the spectrum of the stalk at an
elementary étale neighbourhood.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite-type quasicoherent module that is flat over the base at a point has free sections
on an affine open containing the induced point after an affine elementary étale refinement and
base change to the spectrum of the selected stalk. -/
@[stacks 05MF]
theorem existsAffineOpenWithFreeSections
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (x : X) (h_flat : flatOverAt F f x) :
    ∃ U : EtaleNeighborhood.Elementary S (f x),
      let E := U.obj
      let T := E.toEtale.left
      let R := T.presheaf.stalk E.point
      let b := T.fromSpecStalk E.point ≫ E.toEtale.hom
      let P := Limits.pullback f b
      ∃ _ : IsAffine T,
        let F' := baseChangeModule f b F
        ∃ x' : P,
          Limits.pullback.fst f b x' = x ∧
            Limits.pullback.snd f b x' = IsLocalRing.closedPoint R ∧
              ∃ V : P.Opens, x' ∈ V ∧ IsAffineOpen V ∧
                Module.Free R
                  (Scheme.Hom.sectionsModOverSpec (Limits.pullback.snd f b) V
                    F' : ModuleCat R) := sorry

end AlgebraicGeometry.Scheme.Modules
