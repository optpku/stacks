module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.HigherDirectImage

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace EtaleBaseChange

/-! Types of arbitrary image-functor families and comparison morphisms.
These abbreviations fix the sheaf and derived categories without imposing
canonicality or compatibility conditions on the supplied functors or maps. -/

/-- The type of functor families in the inverse-image direction on set-valued
small étale sheaves, indexed by scheme morphisms. -/
abbrev SetInverseImage :=
  forall {A B : Scheme.{u}}, (A ⟶ B) →
    Sheaf B.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf A.smallEtaleTopology (Type (u + 1))

/-- The type of functor families in the direct-image direction on set-valued
small étale sheaves, indexed by scheme morphisms. -/
abbrev SetDirectImage :=
  forall {A B : Scheme.{u}}, (A ⟶ B) →
    Sheaf A.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf B.smallEtaleTopology (Type (u + 1))

/-- The morphism type between the two set-valued composites of supplied
image-functor families along a square of scheme morphisms. -/
abbrev SetBaseChangeMap
    (invImage : SetInverseImage.{u}) (directImage : SetDirectImage.{u})
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
    (g : T ⟶ S) (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :=
    (invImage f).obj ((directImage g).obj F) ⟶
      (directImage h).obj ((invImage e).obj F)

/-- The type of functor families in the inverse-image direction on derived
categories of abelian étale sheaves, indexed by scheme morphisms. -/
abbrev DerivedInverseImage
    [forall Z : Scheme.{u},
      Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{v})]
    [forall Z : Scheme.{u},
      HasDerivedCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{v})] :=
  forall {A B : Scheme.{u}}, (A ⟶ B) →
    DerivedCategory (Sheaf B.smallEtaleTopology AddCommGrpCat.{v}) ⥤
      DerivedCategory (Sheaf A.smallEtaleTopology AddCommGrpCat.{v})

/-- The type of functor families in the direct-image direction on derived
categories of abelian étale sheaves, indexed by scheme morphisms. -/
abbrev DerivedDirectImage
    [forall Z : Scheme.{u},
      Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{v})]
    [forall Z : Scheme.{u},
      HasDerivedCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{v})] :=
  forall {A B : Scheme.{u}}, (A ⟶ B) →
    DerivedCategory (Sheaf A.smallEtaleTopology AddCommGrpCat.{v}) ⥤
      DerivedCategory (Sheaf B.smallEtaleTopology AddCommGrpCat.{v})

/-- The morphism type between the two derived composites of supplied
image-functor families along a square of scheme morphisms. -/
abbrev DerivedBaseChangeMap
    [forall Z : Scheme.{u},
      Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{v})]
    [forall Z : Scheme.{u},
      HasDerivedCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{v})]
    (invImage : DerivedInverseImage.{u, v})
    (directImage : DerivedDirectImage.{u, v})
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T)
    (g : T ⟶ S)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{v})) :=
    (invImage f).obj ((directImage g).obj K) ⟶
      (directImage h).obj ((invImage e).obj K)

/-- The morphism type between the degree-`q` higher-direct-image composites
formed with a supplied family of inverse-image-direction functors. -/
abbrev HigherBaseChangeMap
    (invImage : forall {A B : Scheme.{u}}, (A ⟶ B) →
      Sheaf B.smallEtaleTopology AddCommGrpCat.{u} ⥤
        Sheaf A.smallEtaleTopology AddCommGrpCat.{u})
    {X Y S T : Scheme.{u}}
    [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [HasInjectiveResolutions
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
    (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S) (q : ℕ)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u}) :=
    (invImage f).obj
        ((Sheaf.higherDirectImageFunctor (Scheme.smallEtalePullback g) q).obj F) ⟶
      (Sheaf.higherDirectImageFunctor (Scheme.smallEtalePullback h) q).obj
        ((invImage e).obj F)

end EtaleBaseChange
