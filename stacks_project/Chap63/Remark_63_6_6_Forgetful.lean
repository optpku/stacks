module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.CategoryTheory.Category.Pointed.Limits
public import stacks_project.Chap59.Lemma_59_29_7

/-!
# Forgetful functor from abelian groups to pointed types

The coefficient forgetful functor `AddCommGrpCat ⥤ Pointed` and the induced
forgetful functor on small-étale sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AddCommGrpCat

/-- The forgetful functor from abelian groups to pointed types, sending a group
to the pointed type with distinguished point `0`. -/
def toPointed : AddCommGrpCat.{u} ⥤ Pointed.{u} where
  obj A := Pointed.of (0 : A)
  map f := ⟨f.hom, map_zero f.hom⟩
  map_id := sorry
  map_comp := sorry

/-- The underlying type of `toPointed.obj A` is the carrier of `A`. -/
theorem toPointed_obj (A : AddCommGrpCat.{u}) : (toPointed.obj A).X = A :=
  sorry

/-- `toPointed` sends the zero of a group homomorphism to the target zero. -/
theorem toPointed_map_point {A B : AddCommGrpCat.{u}} (f : A ⟶ B) :
    (toPointed.map f).toFun (0 : A) = (0 : B) :=
  sorry

/-- The canonical comparison from the pointed coproduct of forgotten groups to
the forgotten coproduct of groups. -/
def toPointedCoprodComparison {ι : Type u} (A : ι → AddCommGrpCat.{u})
    [HasCoproduct fun i : ι ↦ toPointed.obj (A i)] [HasCoproduct A] :
    (∐ fun i : ι ↦ toPointed.obj (A i)) ⟶ toPointed.obj (∐ A) :=
  Sigma.desc fun i ↦ toPointed.map (Sigma.ι A i)

/-- The coproduct comparison is induced by the images of the coproduct
inclusions. -/
theorem toPointedCoprodComparison_ι {ι : Type u} (A : ι → AddCommGrpCat.{u})
    [HasCoproduct fun i : ι ↦ toPointed.obj (A i)] [HasCoproduct A] (i : ι) :
    Sigma.ι (fun j : ι ↦ toPointed.obj (A j)) i ≫ toPointedCoprodComparison A =
      toPointed.map (Sigma.ι A i) :=
  sorry

/-- Abelian groups forget to pointed types by taking the zero element as the
distinguished point. -/
instance : HasForget₂ AddCommGrpCat Pointed where
  forget₂ := toPointed
  forget_comp := sorry

end AddCommGrpCat

namespace AlgebraicGeometry.Scheme.Etale

/-- The forgetful functor from abelian sheaves on the small étale site of `X` to
sheaves of pointed sets. -/
def etaleForgetfulPointed (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology Pointed.{u} :=
  sheafCompose X.smallEtaleTopology AddCommGrpCat.toPointed

/-- Evaluating the étale forgetful functor composes the underlying presheaf with
`AddCommGrpCat.toPointed`. -/
theorem etaleForgetfulPointed_obj (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((etaleForgetfulPointed X).obj F).1 = F.1 ⋙ AddCommGrpCat.toPointed :=
  sorry

/-- Morphisms of abelian étale sheaves are sent to the image under
`AddCommGrpCat.toPointed` on sections. -/
theorem etaleForgetfulPointed_map (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G)
    (U : X.Etaleᵒᵖ) :
    ((etaleForgetfulPointed X).map φ).hom.app U =
      AddCommGrpCat.toPointed.map (φ.hom.app U) :=
  sorry

variable [PreservesFilteredColimits AddCommGrpCat.toPointed]

/-- Geometric stalks commute with the forgetful functor from abelian groups to
pointed types. -/
def etaleForgetfulPointed_sheafFiberIso (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    (z : GeometricPoint X) :
    etaleForgetfulPointed X ⋙ (GeometricPoint.toSmallEtalePoint z).sheafFiber ≅
      (GeometricPoint.toSmallEtalePoint z).sheafFiber ⋙ AddCommGrpCat.toPointed :=
  (GeometricPoint.toSmallEtalePoint z).sheafFiberCompIso AddCommGrpCat.toPointed

/-- Evaluating `etaleForgetfulPointed_sheafFiberIso` on an abelian sheaf is the
stalk comparison of `sheafFiberCompIso`. -/
theorem etaleForgetfulPointed_sheafFiberIso_app (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    (z : GeometricPoint X) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleForgetfulPointed_sheafFiberIso X z).app G =
      ((GeometricPoint.toSmallEtalePoint z).sheafFiberCompIso
        AddCommGrpCat.toPointed).app G :=
  sorry

/-- The mate of `etaleForgetfulPointed_sheafFiberIso` along the skyscraper
adjunctions, sending forgotten abelian skyscrapers to pointed skyscrapers of
forgotten coefficients. -/
def etaleForgetfulPointed_skyscraperIsoHom (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    (z : GeometricPoint X) :
    (GeometricPoint.toSmallEtalePoint z).skyscraperSheafFunctor ⋙
        etaleForgetfulPointed X ⟶
      AddCommGrpCat.toPointed ⋙
        (GeometricPoint.toSmallEtalePoint z).skyscraperSheafFunctor :=
  mateEquiv
    (GeometricPoint.toSmallEtalePoint z).skyscraperSheafAdjunction
    (GeometricPoint.toSmallEtalePoint z).skyscraperSheafAdjunction
    (etaleForgetfulPointed_sheafFiberIso X z).hom

/-- The mate of the forgetful stalk iso along `sheafFiber ⊣ skyscraperSheafFunctor`
is an isomorphism. -/
instance etaleForgetfulPointed_skyscraperIsoHom_isIso (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    (z : GeometricPoint X) :
    IsIso (etaleForgetfulPointed_skyscraperIsoHom X z) :=
  sorry

/-- Forgetting abelian skyscrapers at a geometric point yields pointed
skyscrapers of the forgotten coefficients, naturally in the coefficient. -/
def etaleForgetfulPointed_skyscraperIso (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    (z : GeometricPoint X) :
    (GeometricPoint.toSmallEtalePoint z).skyscraperSheafFunctor ⋙
        etaleForgetfulPointed X ≅
      AddCommGrpCat.toPointed ⋙
        (GeometricPoint.toSmallEtalePoint z).skyscraperSheafFunctor :=
  asIso (etaleForgetfulPointed_skyscraperIsoHom X z)

/-- The forward map of `etaleForgetfulPointed_skyscraperIso` is the mate of
`etaleForgetfulPointed_sheafFiberIso` along the skyscraper adjunctions. -/
theorem etaleForgetfulPointed_skyscraperIso_hom (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    (z : GeometricPoint X) :
    (etaleForgetfulPointed_skyscraperIso X z).hom =
      etaleForgetfulPointed_skyscraperIsoHom X z :=
  sorry

/-- The mate of the forgetful stalk iso is characterized by the skyscraper
adjunction counits. -/
theorem etaleForgetfulPointed_skyscraperIso_counit (X : Scheme.{u})
    [X.smallEtaleTopology.HasSheafCompose AddCommGrpCat.toPointed]
    (z : GeometricPoint X) (A : AddCommGrpCat.{u}) :
    (GeometricPoint.toSmallEtalePoint z).sheafFiber.map
        ((etaleForgetfulPointed_skyscraperIso X z).hom.app A) ≫
      (GeometricPoint.toSmallEtalePoint z).skyscraperSheafAdjunction.counit.app
        (AddCommGrpCat.toPointed.obj A) =
    (etaleForgetfulPointed_sheafFiberIso X z).hom.app
        ((GeometricPoint.toSmallEtalePoint z).skyscraperSheafFunctor.obj A) ≫
      AddCommGrpCat.toPointed.map
        ((GeometricPoint.toSmallEtalePoint z).skyscraperSheafAdjunction.counit.app A) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
