module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Two-morphism rigidity for small étale ringed topoi of algebraic spaces

Every two-endomorphism of the small étale ringed-topos morphism induced by a morphism of
algebraic spaces is the identity.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every two-endomorphism of the small étale ringed-topos morphism induced by a morphism
of algebraic spaces over a scheme is the identity two-morphism. -/
theorem smallEtaleRingedTopos_twoMorphism_eq_id {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    (t : TwoMorphism.{u + 1, u, u + 1, u, u} (ringedToposHom f) (ringedToposHom f)) :
    t = TwoMorphism.refl.{u + 1, u, u + 1, u, u} (ringedToposHom f) := sorry

end AlgebraicGeometry.AlgebraicSpace
