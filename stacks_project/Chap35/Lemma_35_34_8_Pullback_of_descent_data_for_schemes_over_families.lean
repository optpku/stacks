module

import ReasLib.AlgebraicGeometry.Scheme.DescentData.Pullback.Family
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

variable {S S' Y : Scheme.{u}}
variable {𝒰 : SemiRepresentableFamily.Over.{v} S'}
variable {𝒱 : SemiRepresentableFamily.Over.{w} S}
variable {base : S' ⟶ S}
variable
  (φ φ' : SemiRepresentableFamily.Over.Hom
    (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱)
variable
  (D : Scheme.DescentData
    (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom))
variable [Small.{u} 𝒰.index] [Small.{u} 𝒱.index]

/- Lemma 35.34.8 (Pullback of descent data for schemes over families) (1): the pullback
construction acts componentwise by pullback along the maps of the family morphism. -/
@[stacks 02VS] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.functorOfHom_obj_obj φ D :
    ∀ i : 𝒰.index,
      ((AlgebraicGeometry.Scheme.DescentData.Pullback.functorOfHom φ).obj D).obj i =
        (Over.pullback (φ.f i).left).obj (D.obj (φ.α i)))

/- Lemma 35.34.8 (Pullback of descent data for schemes over families) (2): the transition
maps are the pseudofunctorial pullbacks of the corresponding transition maps. -/
@[stacks 02VS] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.functorOfHom_obj_hom φ D :
    ∀ (q : Y ⟶ S') {i i' : 𝒰.index}
      (f : Y ⟶ (𝒰.obj i).left) (f' : Y ⟶ (𝒰.obj i').left)
      (hf : f ≫ (𝒰.obj i).hom = q) (hf' : f' ≫ (𝒰.obj i').hom = q),
      ((AlgebraicGeometry.Scheme.DescentData.Pullback.functorOfHom φ).obj D).hom
          q f f' hf hf' =
        Pseudofunctor.DescentData.pullFunctorObjHom
          (F := Scheme.overPseudofunctor)
          (f := fun j : 𝒱.index ↦ (𝒱.obj j).hom) (p := base)
          (f' := fun j : 𝒰.index ↦ (𝒰.obj j).hom) (α := φ.α)
          (p' := fun j ↦ (φ.f j).left)
          (w := SemiRepresentableFamily.Over.Hom.map_hom base φ)
          D q f f' hf hf')

/- Lemma 35.34.8 (Pullback of descent data for schemes over families) (3): componentwise
pullback defines a contravariant functor from descent data on the target family to descent data
on the source family. -/
@[stacks 02VS] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.functorOfHom (base := base) :
    (φ : SemiRepresentableFamily.Over.Hom
      (SemiRepresentableFamily.Over.map (Over.map base) 𝒰) 𝒱) →
      Scheme.DescentData
          (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) ⥤
        Scheme.DescentData
          (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom))

/- Lemma 35.34.8 (Pullback of descent data for schemes over families) (4): two family
morphisms over the same base map induce canonically isomorphic pullback functors. -/
@[stacks 02VS] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.isoOfHom φ φ' :
    AlgebraicGeometry.Scheme.DescentData.Pullback.functorOfHom φ ≅
      AlgebraicGeometry.Scheme.DescentData.Pullback.functorOfHom φ')

/- Lemma 35.34.8 (Pullback of descent data for schemes over families) (5): under the
coproduct equivalences, family pullback agrees with singleton-family pullback along the induced
map of coproducts. -/
@[stacks 02VS] #check
  (AlgebraicGeometry.Scheme.DescentData.Pullback.coproductIsoOfHom φ :
    (Scheme.DescentData.coproductEquivalence
        (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom)).functor ⋙
      Scheme.DescentData.Pullback.functor
        (Scheme.DescentData.coproductArrow
          (fun j ↦ (𝒱.obj j).left) (fun j ↦ (𝒱.obj j).hom) PUnit.unit)
        (Scheme.DescentData.coproductArrow
          (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom) PUnit.unit)
        base
        (AlgebraicGeometry.Scheme.DescentData.Pullback.coproductMapOfHom φ)
        (CommSq.mk
          (AlgebraicGeometry.Scheme.DescentData.Pullback.coproductMapOfHom_fac φ)) ≅
      AlgebraicGeometry.Scheme.DescentData.Pullback.functorOfHom φ ⋙
        (Scheme.DescentData.coproductEquivalence
          (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom)).functor)
