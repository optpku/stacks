module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Pullback
import StacksCheckRecall

open CategoryTheory

universe u v w

/- Lemma 35.2.2 (1): pull descent data back componentwise along a morphism of fixed-target
families. -/
@[stacks 023C] #check
  (@AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback.functorOfHom_obj_obj :
    ∀ {U V : AlgebraicGeometry.Scheme.{u}} {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.Scheme.{u}}
      {Vⱼ : J → AlgebraicGeometry.Scheme.{u}}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
      (D : AlgebraicGeometry.Scheme.QCoh.DescentData Vⱼ v) (i : I),
      ((AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback.functorOfHom
        α gᵢ comm).obj D).obj.obj i =
        (AlgebraicGeometry.Scheme.Modules.pullback (gᵢ i)).obj (D.obj.obj (α i)))

#check
  (@AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback.functorOfHom_obj_hom :
    ∀ {U V : AlgebraicGeometry.Scheme.{u}} {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.Scheme.{u}}
      {Vⱼ : J → AlgebraicGeometry.Scheme.{u}}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
      (D : AlgebraicGeometry.Scheme.QCoh.DescentData Vⱼ v)
      {Y : AlgebraicGeometry.Scheme.{u}} (q : Y ⟶ U) {i j : I}
      (f₁ : Y ⟶ Uᵢ i) (f₂ : Y ⟶ Uᵢ j)
      (hf₁ : f₁ ≫ u i = q) (hf₂ : f₂ ≫ u j = q),
      ((AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback.functorOfHom
        α gᵢ comm).obj D).obj.hom q f₁ f₂ hf₁ hf₂ =
        Pseudofunctor.DescentData.pullFunctorObjHom
          (F := AlgebraicGeometry.Scheme.Modules.descentPseudofunctor)
          (f := v) (p := base) (f' := u) (α := α) (p' := gᵢ) (w := comm)
          D.obj q f₁ f₂ hf₁ hf₂)

/- Lemma 35.2.2 (2): pullback along a morphism of fixed-target families is functorial on descent
data. -/
@[stacks 023C] #check
  (@AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback.functorOfHom :
    ∀ {U V : AlgebraicGeometry.Scheme.{u}} {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.Scheme.{u}}
      {Vⱼ : J → AlgebraicGeometry.Scheme.{u}}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base),
      AlgebraicGeometry.Scheme.QCoh.DescentData Vⱼ v ⥤
        AlgebraicGeometry.Scheme.QCoh.DescentData Uᵢ u)

#check
  (@AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback.functorOfHom_map_hom :
    ∀ {U V : AlgebraicGeometry.Scheme.{u}} {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.Scheme.{u}}
      {Vⱼ : J → AlgebraicGeometry.Scheme.{u}}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
      {D E : AlgebraicGeometry.Scheme.QCoh.DescentData Vⱼ v}
      (η : D ⟶ E) (i : I),
      ((AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback.functorOfHom
        α gᵢ comm).map η).hom.hom i =
        (AlgebraicGeometry.Scheme.Modules.pullback (gᵢ i)).map (η.hom.hom (α i)))

/- Lemma 35.2.2 (3): two family morphisms over the same base map induce naturally isomorphic
pullback functors. -/
@[stacks 023C] #check
  (@AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback.isoOfHom :
    ∀ {U V : AlgebraicGeometry.Scheme.{u}} {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.Scheme.{u}}
      {Vⱼ : J → AlgebraicGeometry.Scheme.{u}}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
      (α' : I → J) (gᵢ' : ∀ i, Uᵢ i ⟶ Vⱼ (α' i))
      (comm' : ∀ i, gᵢ' i ≫ v (α' i) = u i ≫ base),
      AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback.functorOfHom α gᵢ comm ≅
        AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback.functorOfHom α' gᵢ' comm')

#check
  (@AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback.isoOfHom_hom_app_hom :
    ∀ {U V : AlgebraicGeometry.Scheme.{u}} {I : Type v} {J : Type w}
      {Uᵢ : I → AlgebraicGeometry.Scheme.{u}}
      {Vⱼ : J → AlgebraicGeometry.Scheme.{u}}
      {u : ∀ i, Uᵢ i ⟶ U} {v : ∀ j, Vⱼ j ⟶ V}
      {base : U ⟶ V}
      (α : I → J) (gᵢ : ∀ i, Uᵢ i ⟶ Vⱼ (α i))
      (comm : ∀ i, gᵢ i ≫ v (α i) = u i ≫ base)
      (α' : I → J) (gᵢ' : ∀ i, Uᵢ i ⟶ Vⱼ (α' i))
      (comm' : ∀ i, gᵢ' i ≫ v (α' i) = u i ≫ base)
      (D : AlgebraicGeometry.Scheme.QCoh.DescentData Vⱼ v) (i : I),
      ((AlgebraicGeometry.Scheme.QCoh.DescentData.Pullback.isoOfHom
        α gᵢ comm α' gᵢ' comm').hom.app D).hom.hom i =
        ((Pseudofunctor.DescentData.pullFunctorIso
          (F := AlgebraicGeometry.Scheme.Modules.descentPseudofunctor)
          (f := v) (p := base) (f' := u) (α := α) (p' := gᵢ) (w := comm)
          (β := α') (p'' := gᵢ') comm').hom.app D.obj).hom i)
