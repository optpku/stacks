module

public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.EtaleProjectiveCover
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.LocallyProjective.Affine

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finitely presented module flat at a point over a locally finitely presented morphism
has projective sections on an affine neighbourhood of a point above it after an affine
elementary étale base refinement. -/
theorem existsAffineOpenWithProjectiveSections {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (x : X) (h_flat : flatOverAt F f x) :
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
                Module.Projective Γ(S'.toEtale.left, ⊤) M := sorry

end AlgebraicGeometry.Scheme.Modules
