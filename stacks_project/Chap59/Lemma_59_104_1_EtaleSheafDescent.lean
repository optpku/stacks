module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafPseudofunctor

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheaf

#check (pullback : {X Y : Scheme.{u}} → (X ⟶ Y) →
  Sheaf Y.smallEtaleTopology (Type (u + 1)) ⥤
    Sheaf X.smallEtaleTopology (Type (u + 1)))
#check (pullbackId : (X : Scheme.{u}) →
  pullback (𝟙 X) ≅ 𝟭 (Sheaf X.smallEtaleTopology (Type (u + 1))))
#check (pullbackComp : {X Y Z : Scheme.{u}} → (f : Y ⟶ Z) → (g : X ⟶ Y) →
  pullback f ⋙ pullback g ≅ pullback (g ≫ f))
#check (pseudofunctor : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat)
#check (pseudofunctor_obj : (X : Scheme.{u}) →
  pseudofunctor.obj (.mk (.op X)) =
    Cat.of (Sheaf X.smallEtaleTopology (Type (u + 1))))
#check (pseudofunctor_map : {X Y : Scheme.{u}} → (f : X ⟶ Y) →
  (pseudofunctor.map f.op.toLoc).toFunctor = pullback f)

end AlgebraicGeometry.Scheme.EtaleSheaf
