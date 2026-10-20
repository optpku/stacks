module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.CotangentMap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.DottedArrowMap
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry
open scoped DualNumber

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

/- Exercise 111.35.10 (1): a morphism `f : X ⟶ Y` of schemes over `S`, at a
point `x` with `y = f x`, induces a natural linear map `df : T_{X/S,x} ⟶
T_{Y/S,y}` whenever `κ(y) → κ(x)` is bijective. -/
@[stacks 029L] #check
  (AlgebraicGeometry.Scheme.Hom.relativeTangentMapAt :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
      (hκ : Function.Bijective (f.residueFieldMap x).hom),
      let _ : Module (Y.residueField (f x)) (tangentSpaceAt (f ≫ g) x) :=
        Module.compHom (tangentSpaceAt (f ≫ g) x)
          (RingEquiv.ofBijective (f.residueFieldMap x).hom hκ).toRingHom
      tangentSpaceAt (f ≫ g) x →ₗ[Y.residueField (f x)]
        tangentSpaceAt g (f x))

/- Exercise 111.35.10 (2): if in addition `κ(x) = κ(s)`, the tangent map
matches the dual of the fibre-cotangent map of local rings from Exercise
111.35.2 after the inverse residue-field transport. -/
@[stacks 029L] #check
  (AlgebraicGeometry.Scheme.Hom.relativeTangentMapAt_cotangentLinearDual :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
      (hκ : Function.Bijective (f.residueFieldMap x).hom)
      (hκs : Function.Bijective ((f ≫ g).residueFieldMap x).hom)
      (D : tangentSpaceAt (f ≫ g) x)
      (v : IsLocalRing.CotangentSpace (fiberStalkAt g (f x))),
      relativeTangentSpaceToCotangentLinearDual g (f x)
          (residueFieldMap_bijective_of_triangle f g x hκ hκs)
          (relativeTangentMapAt f g x hκ D) v =
        (RingEquiv.ofBijective (f.residueFieldMap x).hom hκ).symm
          (relativeTangentSpaceToCotangentLinearDual (f ≫ g) x hκs D
            (relativeFiberCotangentMapAt f g x hκ v)))

/- The tangent map is also characterized by its action on dotted dual-number arrows. -/
#check
  (AlgebraicGeometry.Scheme.Hom.relativeTangentMapAt_dottedArrow :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
      (hκ : Function.Bijective (f.residueFieldMap x).hom)
      (D : tangentSpaceAt (f ≫ g) x),
      ((dottedTangentArrowEquiv (f ≫ g) x).symm D).val ≫ f =
        Spec.map (dualNumberResidueFieldMap f x) ≫
          ((dottedTangentArrowEquiv g (f x)).symm
            (relativeTangentMapAt f g x hκ D)).val)

end AlgebraicGeometry.Scheme.Hom
