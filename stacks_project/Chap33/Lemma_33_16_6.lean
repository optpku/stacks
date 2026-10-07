module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Map
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 33.16.6: for composable scheme morphisms `f : X ⟶ Y` and `g : Y ⟶ S`, a point
`x : X`, and a bijective residue-field map `κ(f x) ⟶ κ(x)`, the induced tangent map is
pointwise dual to the induced map on relative Kähler differentials. -/
@[stacks 0B2F] #check
  (AlgebraicGeometry.Scheme.Hom.relativeTangentMapAt_dual :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
      (hκ : Function.Bijective (AlgebraicGeometry.Scheme.Hom.residueFieldMap f x).hom)
      (D : AlgebraicGeometry.Scheme.Hom.tangentSpaceAt (f ≫ g) x)
      (ω : CommRingCat.KaehlerDifferential (g.stalkMap (f x))),
      AlgebraicGeometry.Scheme.Hom.relativeTangentSpaceLinearDual g (f x)
          (AlgebraicGeometry.Scheme.Hom.relativeTangentMapAt f g x hκ D) ω =
        (RingEquiv.ofBijective
          (AlgebraicGeometry.Scheme.Hom.residueFieldMap f x).hom hκ).symm
          (AlgebraicGeometry.Scheme.Hom.relativeTangentSpaceLinearDual (f ≫ g) x D
            (AlgebraicGeometry.Scheme.Hom.relativeCotangentMapAt f g x ω)))
