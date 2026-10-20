module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalLifts.Presheaf

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver

universe u

/- The presheaf of isomorphism classes of infinitesimal lifts on affine test
objects over the thickened base. -/
#check (AlgebraicGeometry.GroupoidsOver.infinitesimalLiftPresheaf :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {A A' : CommRingCat.{u}} {σA : Spec A ⟶ S} {σA' : Spec A' ⟶ S}
    (fA : A' ⟶ A) (hfA : Spec.map fA ≫ σA' = σA)
    (x : X.p.Fiber (Over.mk σA)),
    (Spec A').AffineOverᵒᵖ ⥤ Type (u + 1))
