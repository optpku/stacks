module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.TangentSpace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 33.16.8: for a morphism `f : X ⟶ Y` over `S` whose composite structure map
`f ≫ g : X ⟶ S` is locally of finite type, and a point `x : X` at which the induced
residue-field map is bijective, the relative tangent map is injective if and only if `f` is
unramified at `x`. -/
@[stacks 0B2G] #check
  (AlgebraicGeometry.Scheme.Hom.injective_relativeTangentMapAt_iff_unramifiedAt :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
      [LocallyOfFiniteType (f ≫ g)]
      (hκ : Function.Bijective (Scheme.Hom.residueFieldMap f x).hom),
      Function.Injective (relativeTangentMapAt f g x hκ) ↔ f.UnramifiedAt x)

end AlgebraicGeometry.Scheme.Hom
