module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Composition
import StacksCheckRecall

/-!
# Composition of successive blowups in a product of ideal sheaves

A blowup in a quasi-coherent ideal, followed by a blowup in the inverse image
of a second quasi-coherent ideal, is a blowup in the product ideal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.17.10: successive blowups in two quasi-coherent ideals are
canonically isomorphic over the base to a blowup in their product. -/
@[stacks 085Y] #check (AlgebraicGeometry.AlgebraicSpace.Blowup.isoOver_comp :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I J : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent J]
    (π : Blowup X I) (π' : Blowup π.space (J.pullback π.hom))
    (ρ : Blowup X (IdealSubobject.mul I J)),
    ∃! e : Over.mk (π'.hom ≫ π.hom) ≅ Over.mk ρ.hom,
      e.hom.left ≫ ρ.hom = π'.hom ≫ π.hom)

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.compIsBlowup :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I J : IdealSubobject X) [IsQuasiCoherent I] [IsQuasiCoherent J]
    (π : Blowup X I) (π' : Blowup π.space (J.pullback π.hom)),
    IsBlowup (π'.hom ≫ π.hom) (Blowup.center (IdealSubobject.mul I J)))
