module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Set
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

variable {W X Y S T : Scheme.{u}}

/-- The derived inverse-image square associated to a cartesian square of schemes. -/
noncomputable def squareIso (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (cart : IsPullback h e f g) :
    Derived.inverseImage f ⋙ Derived.inverseImage h ≅
      Derived.inverseImage g ⋙ Derived.inverseImage e :=
  (Derived.inverseImageCompIso h f).symm ≪≫
    eqToIso (congrArg Derived.inverseImage cart.w) ≪≫
    Derived.inverseImageCompIso e g

/-- The canonical derived comparison component associated to a commutative square of schemes. -/
noncomputable def derivedMapOfCommSq {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (square : CommSq g' f' f g)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (Derived.inverseImage g).obj ((Derived.directImage f).obj E) ⟶
      (Derived.directImage f').obj ((Derived.inverseImage g').obj E) :=
  let squareIso :=
    (Derived.inverseImageCompIso f' g).symm ≪≫
      eqToIso (congrArg Derived.inverseImage square.w.symm) ≪≫
      Derived.inverseImageCompIso g' f
  CategoryTheory.DerivedBaseChange.app (Derived.adjunction f) (Derived.adjunction f') squareIso E

/-- The canonical derived base-change component for a cartesian square of schemes. -/
noncomputable def derivedMap (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (cart : IsPullback h e f g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (Derived.inverseImage f).obj ((Derived.directImage g).obj K) ⟶
      (Derived.directImage h).obj ((Derived.inverseImage e).obj K) :=
  CategoryTheory.DerivedBaseChange.app (Derived.adjunction g) (Derived.adjunction h)
    (squareIso f h e g cart) K

/-- The canonical degree-`q` higher-direct-image base-change component for a cartesian square. -/
noncomputable def higherMap (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (cart : IsPullback h e f g) (q : ℕ)
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Abelian.inverseImage f).obj ((Derived.higherDirectImage g q).obj F) ⟶
      (Derived.higherDirectImage h q).obj ((Abelian.inverseImage e).obj F) :=
  let K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    (DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F
  let first :=
    (Abelian.inverseImageExact f).homologyIso ((Derived.directImage g).obj K) (q : ℤ) |>.inv
  let second :=
    (DerivedCategory.homologyFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      (derivedMap f h e g cart K)
  let eta := ((Abelian.inverseImageExact e).obj.mapDerivedCategorySingleFunctor 0).hom.app F
  let third :=
    (DerivedCategory.homologyFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).map
      ((Derived.directImage h).map eta)
  first ≫ second ≫ third

/-- The canonical degree-`q` base-change comparison is natural in its coefficient sheaf. -/
theorem higherMap_naturality (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (cart : IsPullback h e f g) (q : ℕ)
    {F G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (ι : F ⟶ G) :
    higherMap f h e g cart q F ≫
        (Abelian.inverseImage e ⋙ Derived.higherDirectImage h q).map ι =
      (Derived.higherDirectImage g q ⋙ Abelian.inverseImage f).map ι ≫
        higherMap f h e g cart q G := sorry

/-- The morphism induced on cokernels by the natural degree-`q` base-change comparison. -/
noncomputable def higherCokernelMap (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    (cart : IsPullback h e f g) (q : ℕ)
    {F G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (ι : F ⟶ G) :
    cokernel (higherMap f h e g cart q F) ⟶ cokernel (higherMap f h e g cart q G) :=
  cokernel.map (higherMap f h e g cart q F) (higherMap f h e g cart q G)
    ((Derived.higherDirectImage g q ⋙ Abelian.inverseImage f).map ι)
    ((Abelian.inverseImage e ⋙ Derived.higherDirectImage h q).map ι)
    (higherMap_naturality f h e g cart q ι)

end AlgebraicGeometry.Scheme.Etale.BaseChange

end
