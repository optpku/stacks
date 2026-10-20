module

public import ReasLib.AlgebraicGeometry.FormalScheme.ChosenFppf.Affine
import StacksCheckRecall

/-!
# Remark 87.9.8

Over a terminal base, the functor of points of an EGA affine formal scheme
`Spf(A)` is the fppf-sheaf colimit of `h_Spec(A ⧸ I)` as `I` runs over ideals
of definition. Hence it is a classical affine formal algebraic space, and the
category of affine EGA formal schemes is equivalent to the category of
classical affine formal algebraic spaces.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

namespace AlgebraicGeometry.FormalScheme

/- Remark 87.9.8. The canonical affine functor of points is an equivalence. -/
@[stacks 0AIE] #check (AlgebraicGeometry.FormalScheme.affineSheafOfPoints_isEquivalence :
    ∀
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U))),
    (affineSheafOfPoints 𝒮 S hS h𝒮).IsEquivalence)

#check (AlgebraicGeometry.FormalScheme.isColimit_ofSpfCocone :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S)) (A : TopCommRingCat.{u})
    (hA : TopologicalRing.IsAdmissibleRing A),
    ∃ c : Cocone (ofSpfIdealOfDefinitionDiagram 𝒮 S hS A),
      Nonempty (IsColimit c) ∧
        Nonempty (c.pt ≅ (sheafOfPoints 𝒮 S).obj (ofSpf A hA)))

#check (AlgebraicGeometry.FormalScheme.isClassicalAffine_sheafOfPoints_ofSpf :
    ∀
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A)
    (hsize : ∃ T : 𝒮.carrier, (ofSpf A hA).size ≤ (𝒮.toScheme.obj T).size),
    IsClassicalAffine ((sheafOfPoints 𝒮 S).obj (ofSpf A hA)))

#check (AlgebraicGeometry.FormalScheme.sheafOfPoints_map_bijective :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    {X Y : FormalScheme.{u}} [IsAffine X] [IsAffine Y]
    (hX : ∃ T, X.size ≤ (𝒮.toScheme.obj T).size),
    Function.Bijective
      ((sheafOfPoints 𝒮 S).map :
        (X ⟶ Y) → ((sheafOfPoints 𝒮 S).obj X ⟶ (sheafOfPoints 𝒮 S).obj Y)))

#check (AlgebraicGeometry.FormalScheme.exists_isAffine_iso_sheafOfPoints :
    ∀ (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (F : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsClassicalAffine F],
    ∃ (X : FormalScheme.{u}) (_ : IsAffine X),
      Nonempty ((sheafOfPoints 𝒮 S).obj X ≅ F))

end AlgebraicGeometry.FormalScheme
