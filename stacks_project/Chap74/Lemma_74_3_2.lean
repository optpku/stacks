module

public import stacks_project.Chap74.Lemma_74_3_2_Pullback
import StacksCheckRecall

open CategoryTheory

universe u v w

/- Lemma 74.3.2 (1): pull descent data back componentwise along a morphism of fixed-target
families. -/
@[stacks 04W4] #check
  (@AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.functorOfHom_obj_obj :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U V : AlgebraicGeometry.AlgebraicSpace S}
      {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.AlgebraicSpace S}
      {Vⱼ : J → AlgebraicGeometry.AlgebraicSpace S}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
      (D : AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Vⱼ v) (i : I),
      ((AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.functorOfHom
        α gᵢ comm).obj D).obj.obj i =
        (AlgebraicGeometry.AlgebraicSpace.Modules.pullback (gᵢ i)).obj (D.obj.obj (α i)))

#check
  (@AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.functorOfHom_obj_hom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U V : AlgebraicGeometry.AlgebraicSpace S}
      {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.AlgebraicSpace S}
      {Vⱼ : J → AlgebraicGeometry.AlgebraicSpace S}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
      (D : AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Vⱼ v)
      {Y : AlgebraicGeometry.AlgebraicSpace S} (q : Y ⟶ U) {i j : I}
      (f₁ : Y ⟶ Uᵢ i) (f₂ : Y ⟶ Uᵢ j)
      (hf₁ : f₁ ≫ u i = q) (hf₂ : f₂ ≫ u j = q),
      ((AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.functorOfHom
        α gᵢ comm).obj D).obj.hom q f₁ f₂ hf₁ hf₂ =
        Pseudofunctor.DescentData.pullFunctorObjHom
          (F := AlgebraicGeometry.AlgebraicSpace.Modules.descentPseudofunctor S)
          (f := v) (p := base) (f' := u) (α := α) (p' := gᵢ) (w := comm)
          D.obj q f₁ f₂ hf₁ hf₂)

/- Lemma 74.3.2 (2): pullback along a morphism of fixed-target families is functorial on descent
data. -/
@[stacks 04W4] #check
  (@AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.functorOfHom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U V : AlgebraicGeometry.AlgebraicSpace S}
      {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.AlgebraicSpace S}
      {Vⱼ : J → AlgebraicGeometry.AlgebraicSpace S}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base),
      AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Vⱼ v ⥤
        AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Uᵢ u)

#check
  (@AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.functorOfHom_map_hom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U V : AlgebraicGeometry.AlgebraicSpace S}
      {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.AlgebraicSpace S}
      {Vⱼ : J → AlgebraicGeometry.AlgebraicSpace S}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
      {D E : AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Vⱼ v}
      (η : D ⟶ E) (i : I),
      ((AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.functorOfHom
        α gᵢ comm).map η).hom.hom i =
        (AlgebraicGeometry.AlgebraicSpace.Modules.pullback (gᵢ i)).map (η.hom.hom (α i)))

/- Lemma 74.3.2 (3): two family morphisms over the same base map induce naturally isomorphic
pullback functors. -/
@[stacks 04W4] #check
  (@AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.isoOfHom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U V : AlgebraicGeometry.AlgebraicSpace S}
      {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.AlgebraicSpace S}
      {Vⱼ : J → AlgebraicGeometry.AlgebraicSpace S}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
      (α' : I → J) (gᵢ' : ∀ i, Uᵢ i ⟶ Vⱼ (α' i))
      (comm' : ∀ i, gᵢ' i ≫ v (α' i) = u i ≫ base),
      AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.functorOfHom α gᵢ comm ≅
        AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.functorOfHom α' gᵢ' comm')

#check
  (@AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.isoOfHom_hom_app_hom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {U V : AlgebraicGeometry.AlgebraicSpace S}
      {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.AlgebraicSpace S}
      {Vⱼ : J → AlgebraicGeometry.AlgebraicSpace S}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
      (α' : I → J) (gᵢ' : ∀ i, Uᵢ i ⟶ Vⱼ (α' i))
      (comm' : ∀ i, gᵢ' i ≫ v (α' i) = u i ≫ base)
      (D : AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData Vⱼ v) (i : I),
      ((AlgebraicGeometry.AlgebraicSpace.QCoh.DescentData.Pullback.isoOfHom
        α gᵢ comm α' gᵢ' comm').hom.app D).hom.hom i =
        ((Pseudofunctor.DescentData.pullFunctorIso
          (F := AlgebraicGeometry.AlgebraicSpace.Modules.descentPseudofunctor S)
          (f := v) (p := base) (f' := u) (α := α) (p' := gᵢ) (w := comm)
          (β := α') (p'' := gᵢ') comm').hom.app D.obj).hom i)
