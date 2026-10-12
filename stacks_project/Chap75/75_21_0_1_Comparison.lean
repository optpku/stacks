/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologyBaseChange.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition.ExactFirst
public import stacks_project.Chap66.Lemma_66_29_5_Comparison
public import stacks_project.Chap75.Lemma_75_26_3_FiberEulerCharacteristic
public import stacks_project.Chap75.Lemma_75_26_6_Pullback

/-!
# Geometric-point cohomology base change for algebraic spaces

A commutative square of algebraic spaces, a complex `K` in `D_QCoh(𝒪_X)`, and a map
`L(g')^* K ⟶ K'` in `D_QCoh(𝒪_{X'})` determine, at each geometric point `x̄'` and degree
`i`, a canonical `𝒪_{X', x̄'}`-module morphism
`H^i(K_{x̄} ⊗^L_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'}) ⊗_{(𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'})} 𝒪_{X', x̄'} ⟶ H^i(K'_{x̄'})`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open CategoryTheory.Functor.LeftDerived.Homotopy.Composition
open ComplexShape
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

/-- Postcomposition of geometric points is functorial in the morphism. -/
theorem map_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (xbar : GeometricPoint X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    xbar.map (f ≫ g) = (xbar.map f).map g := sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}}

/-- The two image geometric points of `x̄'` in `Y` along a commutative square agree. -/
theorem point_image_eq {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (xbar' : GeometricPoint X') :
    (xbar'.map g').map f = (xbar'.map f').map g := sorry

/-- Transport of étale local rings along equality of geometric points. -/
noncomputable def etaleLocalRingCatCongr {X : AlgebraicSpace S}
    {p q : GeometricPoint X} (h : p = q) :
    CommRingCat.of (etaleLocalRing X p) ⟶ CommRingCat.of (etaleLocalRing X q) :=
  eqToHom (congrArg (fun r ↦ CommRingCat.of (etaleLocalRing X r)) h)

/-- The ring map `𝒪_{Y, ȳ} ⟶ 𝒪_{Y', ȳ'}` at `x̄'`, transporting `etaleLocalRingMap g`
along the identification of the two image points in `Y`. -/
noncomputable def pointBaseChangeRingMap {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (xbar' : GeometricPoint X') :
    CommRingCat.of (etaleLocalRing Y ((xbar'.map g').map f)) ⟶
      CommRingCat.of (etaleLocalRing Y' (xbar'.map f')) :=
  etaleLocalRingCatCongr (point_image_eq g' f' f g h_comm xbar') ≫
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
        (-- Local instance justification (noncanonical choice): the étale local ring map of `f`
         -- fixes the left tensor-factor scalar structure at `x̄'`.
         let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
            (etaleLocalRing X (xbar'.map g')) :=
          (etaleLocalRingMap f (xbar'.map g')).toAlgebra
         -- Local instance justification (noncanonical choice): the transported étale local ring
         -- map of `g` fixes the right tensor-factor scalar structure at `x̄'`.
         let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
            (etaleLocalRing Y' (xbar'.map f')) :=
          (pointBaseChangeRingMap g' f' f g h_comm xbar').hom.toAlgebra
         Algebra.TensorProduct.includeLeftRingHom) =
      etaleLocalRingMap g' xbar' := sorry

/-- The derived object `K_{x̄} ⊗^L_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'}` in
`D(𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} 𝒪_{Y', ȳ'})`. -/
noncomputable def stalkTensor {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (K : DerivedQCoh X)
    (xbar' : GeometricPoint X') :
    DerivedCategory (ModuleCat (pointTensorRing g' f' f g h_comm xbar')) :=
  (ModuleCat.derivedExtensionOfScalars
      (Scheme.DerivedQCoh.baseChangeRingLeftMap
        (CommRingCat.of (etaleLocalRing Y ((xbar'.map g').map f)))
        (CommRingCat.of (etaleLocalRing X (xbar'.map g')))
        (CommRingCat.of (etaleLocalRing Y' (xbar'.map f')))
        (CommRingCat.ofHom (etaleLocalRingMap f (xbar'.map g')))
        (pointBaseChangeRingMap g' f' f g h_comm xbar')).hom).obj
    (ModuleDerived.stalkDerived (xbar'.map g') ((inclusion X).obj K))

/-- Underived pullback-stalk comparison, as a natural transformation. -/
noncomputable def pullbackStalkComparisonNatTrans {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (xbar' : GeometricPoint X') :
    (toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor (structureSheaf X) ⋙
        ModuleCat.extendScalars (etaleLocalRingMap g' xbar') ⟶
      Modules.pullback g' ⋙
        (toSmallEtalePoint xbar').sheafModuleStalkFunctor (structureSheaf X') :=
  { app := fun G ↦ Modules.pullbackStalkComparison g' G xbar'
    naturality := sorry }

/-- The homotopy-to-derived counit of the stalk-then-extend-scalars route. -/
noncomputable def extensionStalkRouteCounit {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (xbar' : GeometricPoint X') :
    (DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X) ⋙
        (((toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor
            (structureSheaf X)).mapDerivedCategory ⋙
          ModuleCat.derivedExtensionOfScalars (etaleLocalRingMap g' xbar')) ⟶
      Functor.Homotopy.toDerived
        ((toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor (structureSheaf X) ⋙
          ModuleCat.extendScalars (etaleLocalRingMap g' xbar')) :=
  ExactFirst.counit
    (ExactFunctor.of
      ((toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor (structureSheaf X)))
    (ModuleCat.extendScalars (etaleLocalRingMap g' xbar'))

/-- The homotopy-to-derived counit of the derived-pullback-then-stalk route. -/
noncomputable def pullbackStalkRouteCounit {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (xbar' : GeometricPoint X') :
    (DerivedCategory.Qh : HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived X) ⋙
        (ModuleDerived.pullback g' ⋙
          ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
            (structureSheaf X')).mapDerivedCategory) ⟶
      Functor.Homotopy.toDerived
        (Modules.pullback g' ⋙
          (toSmallEtalePoint xbar').sheafModuleStalkFunctor (structureSheaf X')) :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.LeftDerived.Homotopy.counit (Modules.pullback g')) _ ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _
            ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
              (structureSheaf X')).mapDerivedCategoryFactorsh.hom ≫
          (toDerivedIso
              ((toSmallEtalePoint xbar').sheafModuleStalkFunctor (structureSheaf X'))
              (Modules.pullback g')
              (Modules.pullback g' ⋙
                (toSmallEtalePoint xbar').sheafModuleStalkFunctor (structureSheaf X'))
              (Iso.refl _)).inv

/-- The derived-pullback-then-stalk route is a left derived functor of its underived composite. -/
instance pullbackStalkRoute_isLeftDerived {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (xbar' : GeometricPoint X') :
    (ModuleDerived.pullback g' ⋙
        ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
          (structureSheaf X')).mapDerivedCategory).IsLeftDerivedFunctor
      (pullbackStalkRouteCounit g' xbar')
      (HomotopyCategory.quasiIso (Modules X) (up ℤ)) := sorry

/-- Derived comparison `(L(g')^* E)_{x̄'} ⟵ E_{x̄} ⊗^L_{𝒪_{X, x̄}} 𝒪_{X', x̄'}`,
as a natural transformation. -/
noncomputable def pullbackStalkDerivedNatTrans {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (xbar' : GeometricPoint X') :
    ((toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor
          (structureSheaf X)).mapDerivedCategory ⋙
        ModuleCat.derivedExtensionOfScalars (etaleLocalRingMap g' xbar') ⟶
      ModuleDerived.pullback g' ⋙
        ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
          (structureSheaf X')).mapDerivedCategory :=
  CategoryTheory.Functor.leftDerivedNatTrans
    (((toSmallEtalePoint (xbar'.map g')).sheafModuleStalkFunctor
        (structureSheaf X)).mapDerivedCategory ⋙
      ModuleCat.derivedExtensionOfScalars (etaleLocalRingMap g' xbar'))
    (ModuleDerived.pullback g' ⋙
      ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
        (structureSheaf X')).mapDerivedCategory)
    (extensionStalkRouteCounit g' xbar') (pullbackStalkRouteCounit g' xbar')
    (HomotopyCategory.quasiIso (Modules X) (up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (pullbackStalkComparisonNatTrans g' xbar') (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat (etaleLocalRing X' xbar')) (up ℤ) ⥤
          DerivedCategory (ModuleCat (etaleLocalRing X' xbar'))))

/-- Derived comparison
`(E_{x̄} ⊗^L_{𝒪_{X, x̄}} 𝒪_{X', x̄'}) ⟶ (L(g')^* E)_{x̄'}`. -/
noncomputable def pullbackStalkDerivedComparison {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (xbar' : GeometricPoint X') (E : ModuleDerived X) :
    (ModuleCat.derivedExtensionOfScalars (etaleLocalRingMap g' xbar')).obj
        (ModuleDerived.stalkDerived (xbar'.map g') E) ⟶
      ModuleDerived.stalkDerived xbar' ((ModuleDerived.pullback g').obj E) :=
  (pullbackStalkDerivedNatTrans g' xbar').app E

/-- The map from the scalar-extended stalk of `K` to the stalk of `K'`, obtained from the
derived pullback-stalk comparison and `α`. -/
noncomputable def pointPullbackStalkMap {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (xbar' : GeometricPoint X') :
    (ModuleCat.derivedExtensionOfScalars (etaleLocalRingMap g' xbar')).obj
        (ModuleDerived.stalkDerived (xbar'.map g') ((inclusion X).obj K)) ⟶
      ModuleDerived.stalkDerived xbar' ((inclusion X').obj K') :=
  pullbackStalkDerivedComparison g' xbar' ((inclusion X).obj K) ≫
    ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
      (structureSheaf X')).mapDerivedCategory.map α

/-- `pointPullbackStalkMap` is the pullback-stalk comparison followed by the stalk of `α`. -/
theorem pointPullbackStalkMap_eq {X' X : AlgebraicSpace S}
    (g' : X' ⟶ X) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (xbar' : GeometricPoint X') :
    pointPullbackStalkMap g' K K' α xbar' =
      pullbackStalkDerivedComparison g' xbar' ((inclusion X).obj K) ≫
        ((toSmallEtalePoint xbar').sheafModuleStalkFunctor
          (structureSheaf X')).mapDerivedCategory.map α := sorry

/-- The canonical derived point comparison.  It first identifies the two-step scalar
extension with extension along `𝒪_{X, x̄} ⟶ 𝒪_{X', x̄'}`, then applies the stalk map
induced by `α`. -/
noncomputable def pointComparisonMap {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (xbar' : GeometricPoint X') :
    (ModuleCat.derivedExtensionOfScalars
        (pointTensorMap g' f' f g h_comm xbar').hom).obj
        (stalkTensor g' f' f g h_comm K xbar') ⟶
      ModuleDerived.stalkDerived xbar' ((inclusion X').obj K') :=
  (ModuleCat.derivedExtensionOfScalarsCompIso
      (Scheme.DerivedQCoh.baseChangeRingLeftMap
        (CommRingCat.of (etaleLocalRing Y ((xbar'.map g').map f)))
        (CommRingCat.of (etaleLocalRing X (xbar'.map g')))
        (CommRingCat.of (etaleLocalRing Y' (xbar'.map f')))
        (CommRingCat.ofHom (etaleLocalRingMap f (xbar'.map g')))
        (pointBaseChangeRingMap g' f' f g h_comm xbar')).hom
      (pointTensorMap g' f' f g h_comm xbar').hom (etaleLocalRingMap g' xbar')
      (pointTensorMap_includeLeft g' f' f g h_comm xbar')).hom.app
    (ModuleDerived.stalkDerived (xbar'.map g') ((inclusion X).obj K)) ≫
    pointPullbackStalkMap g' K K' α xbar'

/-- The canonical degree-`i` cohomology base-change map at a geometric point `x̄'`. -/
noncomputable def pointCohomologyMap {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (xbar' : GeometricPoint X') (i : ℤ) :=
  -- Local instance justification (noncanonical choice): the étale local ring map of `f`
  -- fixes the source-ring action used in the tensor-product coefficient ring.
  let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
      (etaleLocalRing X (xbar'.map g')) :=
    (etaleLocalRingMap f (xbar'.map g')).toAlgebra
  -- Local instance justification (noncanonical choice): the transported étale local ring map
  -- of `g` fixes the changed-base action in the tensor-product coefficient ring.
  let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
      (etaleLocalRing Y' (xbar'.map f')) :=
    (pointBaseChangeRingMap g' f' f g h_comm xbar').hom.toAlgebra
  ModuleCat.cohomologyBaseChangeMap (pointTensorMap g' f' f g h_comm xbar').hom
    (stalkTensor g' f' f g h_comm K xbar')
    (ModuleDerived.stalkDerived xbar' ((inclusion X').obj K'))
    (pointComparisonMap g' f' f g h_comm K K' α xbar') i

/-- `pointCohomologyMap` is the algebraic cohomology base-change map of the geometric-point
comparison. -/
theorem pointCohomologyMap_eq {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h_comm : g' ≫ f = f' ≫ g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (α : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K')
    (xbar' : GeometricPoint X') (i : ℤ) :
    pointCohomologyMap g' f' f g h_comm K K' α xbar' i =
      -- Local instance justification (noncanonical choice): same source-ring action as in
      -- `pointCohomologyMap`.
      let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
          (etaleLocalRing X (xbar'.map g')) :=
        (etaleLocalRingMap f (xbar'.map g')).toAlgebra
      -- Local instance justification (noncanonical choice): same changed-base action as in
      -- `pointCohomologyMap`.
      let _ : Algebra (etaleLocalRing Y ((xbar'.map g').map f))
          (etaleLocalRing Y' (xbar'.map f')) :=
        (pointBaseChangeRingMap g' f' f g h_comm xbar').hom.toAlgebra
      ModuleCat.cohomologyBaseChangeMap (pointTensorMap g' f' f g h_comm xbar').hom
        (stalkTensor g' f' f g h_comm K xbar')
        (ModuleDerived.stalkDerived xbar' ((inclusion X').obj K'))
        (pointComparisonMap g' f' f g h_comm K K' α xbar') i := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

end
