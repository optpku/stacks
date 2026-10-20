module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.BaseChangeHomology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.Functoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Comparison

/-! # Geometric-point cohomology base change for algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- The two image geometric points of `x̄'` in `Y` along a commutative square agree. -/
theorem point_image_eq {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (xbar' : GeometricPoint X') :
    (xbar'.map g').map f = (xbar'.map f').map g := sorry

/-- The ring map `𝒪_{Y, ȳ} ⟶ 𝒪_{Y', ȳ'}` at `x̄'`, transporting `etaleLocalRingMap g`
along the identification of the two image points in `Y`. -/
noncomputable def pointBaseChangeRingMap {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (xbar' : GeometricPoint X') :
    CommRingCat.of (etaleLocalRing Y ((xbar'.map g').map f)) ⟶
      CommRingCat.of (etaleLocalRing Y' (xbar'.map f')) :=
  eqToHom (congrArg (fun p ↦ CommRingCat.of (etaleLocalRing Y p))
      (point_image_eq g' f' f g h_comm xbar')) ≫
    CommRingCat.ofHom (etaleLocalRingMap g (xbar'.map f'))

/-- The four étale local ring maps induced by a commutative square commute. -/
theorem pointRingSquare_comm {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (xbar' : GeometricPoint X') :
    CommRingCat.ofHom (etaleLocalRingMap f (xbar'.map g')) ≫
        CommRingCat.ofHom (etaleLocalRingMap g' xbar') =
      pointBaseChangeRingMap g' f' f g h_comm xbar' ≫
        CommRingCat.ofHom (etaleLocalRingMap f' xbar') := sorry

/-- The tensor-product coefficient ring `𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'}` at `x̄'`. -/
noncomputable abbrev pointTensorRing {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (xbar' : GeometricPoint X') : CommRingCat.{u} :=
  Scheme.DerivedQCoh.baseChangeRing
    (CommRingCat.of (etaleLocalRing Y ((xbar'.map g').map f)))
    (CommRingCat.of (etaleLocalRing X (xbar'.map g')))
    (CommRingCat.of (etaleLocalRing Y' (xbar'.map f')))
    (CommRingCat.ofHom (etaleLocalRingMap f (xbar'.map g')))
    (pointBaseChangeRingMap g' f' f g h_comm xbar')

/-- The canonical ring map
`𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'} ⟶ 𝒪_{X', x̄'}` induced by a commutative square. -/
noncomputable def pointTensorMap {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (xbar' : GeometricPoint X') :
    pointTensorRing g' f' f g h_comm xbar' ⟶
      CommRingCat.of (etaleLocalRing X' xbar') :=
  Scheme.DerivedQCoh.baseChangeRingMap
    (CommRingCat.of (etaleLocalRing Y ((xbar'.map g').map f)))
    (CommRingCat.of (etaleLocalRing X (xbar'.map g')))
    (CommRingCat.of (etaleLocalRing Y' (xbar'.map f')))
    (CommRingCat.of (etaleLocalRing X' xbar'))
    (CommRingCat.ofHom (etaleLocalRingMap f (xbar'.map g')))
    (pointBaseChangeRingMap g' f' f g h_comm xbar')
    (CommRingCat.ofHom (etaleLocalRingMap g' xbar'))
    (CommRingCat.ofHom (etaleLocalRingMap f' xbar'))
    (pointRingSquare_comm g' f' f g h_comm xbar')

/-- `pointTensorMap` restricts to `etaleLocalRingMap g'` on the left tensor factor. -/
theorem pointTensorMap_includeLeft {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (xbar' : GeometricPoint X') :
    (pointTensorMap g' f' f g h_comm xbar').hom.comp
        (Scheme.DerivedQCoh.baseChangeRingLeftMap
          (CommRingCat.of (etaleLocalRing Y ((xbar'.map g').map f)))
          (CommRingCat.of (etaleLocalRing X (xbar'.map g')))
          (CommRingCat.of (etaleLocalRing Y' (xbar'.map f')))
          (CommRingCat.ofHom (etaleLocalRingMap f (xbar'.map g')))
          (pointBaseChangeRingMap g' f' f g h_comm xbar')).hom =
      etaleLocalRingMap g' xbar' := sorry

/-- Restriction of the source stalk to the base local ring, followed by derived extension
of scalars to the changed-base local ring. -/
def stalkBaseChange {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (K : DerivedQCoh X)
    (xbar' : GeometricPoint X') :
    DerivedCategory (ModuleCat.{u} (etaleLocalRing Y' (xbar'.map f'))) :=
  -- Local instance justification (noncanonical choice): the explicit map of source
  -- local rings fixes restriction to the base local ring.
  let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
      (etaleLocalRing X (xbar'.map g')) :=
    (etaleLocalRingMap f (xbar'.map g')).toAlgebra
  -- Local instance justification (noncanonical choice): the transported map of base local
  -- rings fixes extension to the changed-base local ring.
  let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
      (etaleLocalRing Y' (xbar'.map f')) :=
    (pointBaseChangeRingMap g' f' f g h_comm xbar').hom.toAlgebra
  (ModuleCat.Pushout.DerivedExtension.baseDerived
    (R := etaleLocalRing Y ((xbar'.map g').map f))
    (A := etaleLocalRing X (xbar'.map g'))
    (R' := etaleLocalRing Y' (xbar'.map f'))).obj
      (ModuleDerived.stalkDerived (xbar'.map g') ((inclusion X).obj K))

/-- Cohomology of the derived base-changed stalk, with its canonical action by the tensor
product of the source local ring and the changed-base local ring. -/
def pointBaseChangeHomology {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (K : DerivedQCoh X)
    (xbar' : GeometricPoint X') (i : ℤ) :
    ModuleCat.{u} (pointTensorRing g' f' f g h_comm xbar') :=
  -- Local instance justification (noncanonical choice): the explicit map of source
  -- local rings fixes restriction to the base local ring.
  let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
      (etaleLocalRing X (xbar'.map g')) :=
    (etaleLocalRingMap f (xbar'.map g')).toAlgebra
  -- Local instance justification (noncanonical choice): the transported map of base local
  -- rings fixes extension to the changed-base local ring.
  let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
      (etaleLocalRing Y' (xbar'.map f')) :=
    (pointBaseChangeRingMap g' f' f g h_comm xbar').hom.toAlgebra
  ModuleCat.DerivedBaseChange.homologyModule
    (R := etaleLocalRing Y ((xbar'.map g').map f))
    (R' := etaleLocalRing Y' (xbar'.map f'))
    (ModuleDerived.stalkDerived (xbar'.map g') ((inclusion X).obj K)) i

/-- The map from the scalar-extended stalk of `K` to the stalk of `K'`, obtained from the
derived pullback-stalk comparison and `α`. -/
noncomputable def pointPullbackStalkMap {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (xbar' : GeometricPoint X') :
    (ModuleCat.derivedExtensionOfScalars (etaleLocalRingMap g' xbar')).obj
        (ModuleDerived.stalkDerived (xbar'.map g') ((inclusion X).obj K)) ⟶
      ModuleDerived.stalkDerived xbar' ((inclusion X').obj K') :=
  ModuleDerived.pullbackStalkDerivedComparison g' xbar' ((inclusion X).obj K) ≫
    ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
      (structureSheaf X')).mapDerivedCategory.map α

/-- `pointPullbackStalkMap` is the pullback-stalk comparison followed by the stalk of `α`. -/
theorem pointPullbackStalkMap_eq {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (xbar' : GeometricPoint X') :
    pointPullbackStalkMap g' K K' α xbar' =
      ModuleDerived.pullbackStalkDerivedComparison g' xbar' ((inclusion X).obj K) ≫
        ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
          (structureSheaf X')).mapDerivedCategory.map α := sorry

/-- The canonical degreewise map from extended base-change stalk cohomology to the
cohomology of the target stalk, induced by the given derived pullback morphism. -/
def pointCohomologyMap {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (xbar' : GeometricPoint X') (i : ℤ) :
    (ModuleCat.extendScalars (pointTensorMap g' f' f g h_comm xbar').hom).obj
        (pointBaseChangeHomology g' f' f g h_comm K xbar' i) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (etaleLocalRing X' xbar')) i).obj
        (ModuleDerived.stalkDerived xbar' ((inclusion X').obj K')) :=
  -- Local instance justification (noncanonical choice): the explicit map of source
  -- local rings fixes restriction to the base local ring.
  let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
      (etaleLocalRing X (xbar'.map g')) :=
    (etaleLocalRingMap f (xbar'.map g')).toAlgebra
  -- Local instance justification (noncanonical choice): the transported map of base local
  -- rings fixes extension to the changed-base local ring.
  let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
      (etaleLocalRing Y' (xbar'.map f')) :=
    (pointBaseChangeRingMap g' f' f g h_comm xbar').hom.toAlgebra
  ModuleCat.DerivedBaseChange.cohomologyMap
    (R := etaleLocalRing Y ((xbar'.map g').map f))
    (R' := etaleLocalRing Y' (xbar'.map f'))
    (pointTensorMap g' f' f g h_comm xbar').hom (etaleLocalRingMap g' xbar')
    (pointTensorMap_includeLeft g' f' f g h_comm xbar')
    (ModuleDerived.stalkDerived (xbar'.map g') ((inclusion X).obj K))
    (ModuleDerived.stalkDerived xbar' ((inclusion X').obj K'))
    (pointPullbackStalkMap g' K K' α xbar') i

/-- The geometric cohomology map is the algebraic base-change cohomology map formed from
the actual pullback-stalk comparison and the given derived morphism. -/
theorem pointCohomologyMap_eq {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (xbar' : GeometricPoint X') (i : ℤ) :
    pointCohomologyMap g' f' f g h_comm K K' α xbar' i =
      -- Local instance justification (noncanonical choice): the explicit map of source
      -- local rings fixes restriction to the base local ring.
      let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
          (etaleLocalRing X (xbar'.map g')) :=
        (etaleLocalRingMap f (xbar'.map g')).toAlgebra
      -- Local instance justification (noncanonical choice): the transported map of base local
      -- rings fixes extension to the changed-base local ring.
      let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
          (etaleLocalRing Y' (xbar'.map f')) :=
        (pointBaseChangeRingMap g' f' f g h_comm xbar').hom.toAlgebra
      ModuleCat.DerivedBaseChange.cohomologyMap
        (R := etaleLocalRing Y ((xbar'.map g').map f))
        (R' := etaleLocalRing Y' (xbar'.map f'))
        (pointTensorMap g' f' f g h_comm xbar').hom (etaleLocalRingMap g' xbar')
        (pointTensorMap_includeLeft g' f' f g h_comm xbar')
        (ModuleDerived.stalkDerived (xbar'.map g') ((inclusion X).obj K))
        (ModuleDerived.stalkDerived xbar' ((inclusion X').obj K'))
        (pointPullbackStalkMap g' K K' α xbar') i := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

end
