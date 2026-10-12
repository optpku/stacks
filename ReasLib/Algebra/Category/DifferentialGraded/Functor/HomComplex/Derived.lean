/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Localization.Opposite
public import Mathlib.CategoryTheory.Localization.Prod
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.HomComplex
public import ReasLib.CategoryTheory.Linear.Opposite

/-!
# Derived Hom and right-derived mapped Hom

This file owns the `D(R)`-valued enriched Hom bifunctor on a DG homotopy category. Given any
localization of that category, total right derivation in both variables produces `RHom` on
arbitrary localized objects. It also records the separate operation of right-deriving the Hom
bifunctor after an `R`-linear DG functor.

The latter target is the right derived functor of `Hom(F(-), F(-))`. It is not, without further
compatibility hypotheses, the composite of `RHom` with a left-derived functor of `F`. Keeping
these constructions distinct prevents a right-derived replacement in the second variable from
being mistaken for the property-(P) replacement used to compute a left-derived tensor functor.

The construction is independent of resolutions and of any particular DG category. Concrete
property-(P), K-projective, or K-injective models belong in downstream computation modules.
-/

@[expose] public section

noncomputable section

universe u v w h d e

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedCategory.HomComplex.Derived

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w}
variable [DA : DifferentialGradedCategory.{u, v, h} R A]
variable [DB : DifferentialGradedCategory.{u, w, h} R B]
variable [HasDerivedCategory (ModuleCat.{h} R)]

/-- Simultaneous precomposition and postcomposition on an enriched Hom complex. -/
@[stacks 0CS6 "simultaneous precomposition and postcomposition on enriched Hom"]
def compMap {X X' Y Y' : A} (f : CompHom X' X) (g : CompHom Y Y') :
    homComplex X Y ⟶ homComplex X' Y' :=
  HomComplex.precomp f ≫ HomComplex.postcomp g

/-- Homotopic choices in either variable induce the same morphism of Hom objects in `D(R)`. -/
theorem compMap_eq_of_homotopic {X X' Y Y' : A}
    {f f' : CompHom X' X} {g g' : CompHom Y Y'}
    (hf : Homotopic X' X f f') (hg : Homotopic Y Y' g g') :
    DerivedCategory.Q.map (compMap f g) = DerivedCategory.Q.map (compMap f' g') := sorry

/-- The morphism between Hom objects in `D(R)` induced by two morphisms in the DG homotopy
category. -/
@[stacks 0CS6 "homotopy-class map on derived Hom objects"]
noncomputable def mapHomotopy {X X' Y Y' : K R A}
    (f : X' ⟶ X) (g : Y ⟶ Y') :
    DerivedCategory.Q.obj (homComplex X.obj Y.obj) ⟶
      DerivedCategory.Q.obj (homComplex X'.obj Y'.obj) :=
  Quotient.liftOn₂ f g
    (fun f₀ g₀ ↦ DerivedCategory.Q.map (compMap f₀ g₀))
    (fun _ _ _ _ hf hg ↦ compMap_eq_of_homotopic hf hg)

/-- On represented homotopy classes, `mapHomotopy` is localization of simultaneous
precomposition and postcomposition. -/
@[simp]
theorem mapHomotopy_mk {X X' Y Y' : A} (f : CompHom X' X) (g : CompHom Y Y') :
    mapHomotopy f.toHomotopyClass g.toHomotopyClass =
      DerivedCategory.Q.map (compMap f g) := sorry

/-- Simultaneous Hom action sends the identity of a pair of homotopy objects to the identity. -/
theorem mapHomotopy_id (X : (K R A)ᵒᵖ × K R A) :
    mapHomotopy (𝟙 X.1.unop) (𝟙 X.2) =
      𝟙 (DerivedCategory.Q.obj (homComplex X.1.unop.obj X.2.obj)) := sorry

/-- Simultaneous Hom action respects composition of pairs of homotopy morphisms. -/
theorem mapHomotopy_comp {X Y Z : (K R A)ᵒᵖ × K R A}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapHomotopy (f ≫ g).1.unop (f ≫ g).2 =
      mapHomotopy f.1.unop f.2 ≫ mapHomotopy g.1.unop g.2 := sorry

/-- The enriched Hom bifunctor on the DG homotopy category, valued in `D(R)`. -/
@[stacks 0CS6 "derived-category-valued Hom bifunctor of a DG category"]
noncomputable def functor :
    (K R A)ᵒᵖ × K R A ⥤ DerivedCategory (ModuleCat.{h} R) where
  obj X := DerivedCategory.Q.obj (homComplex X.1.unop.obj X.2.obj)
  map f := mapHomotopy f.1.unop f.2
  map_id X := mapHomotopy_id X
  map_comp f g := mapHomotopy_comp f g

/-- The curried derived Hom functor, with the source variable first. -/
@[stacks 0CS6 "curried derived Hom functor"]
noncomputable def curried : (K R A)ᵒᵖ ⥤ K R A ⥤ DerivedCategory (ModuleCat.{h} R) :=
  Functor.curry.obj (functor (R := R) (A := A))

/-- The derived Hom functor with a fixed target and varying source. -/
@[stacks 0CS6 "source-variable derived Hom functor"]
noncomputable def sourceFunctor (Y : K R A) :
    (K R A)ᵒᵖ ⥤ DerivedCategory (ModuleCat.{h} R) :=
  (curried (R := R) (A := A)).flip.obj Y

/-- The derived Hom functor with a fixed source and varying target. -/
@[stacks 0CS6 "target-variable derived Hom functor"]
noncomputable def targetFunctor (X : (K R A)ᵒᵖ) :
    K R A ⥤ DerivedCategory (ModuleCat.{h} R) :=
  (curried (R := R) (A := A)).obj X

/-- The source-variable derived Hom functor is additive. -/
@[stacks 0CS6 "additivity in the source variable of derived Hom"]
noncomputable instance sourceFunctorAdditive (Y : K R A) :
    (sourceFunctor (R := R) (A := A) Y).Additive := sorry

/-- The source-variable derived Hom functor is `R`-linear. -/
@[stacks 0CS6 "linearity in the source variable of derived Hom"]
noncomputable instance sourceFunctorLinear (Y : K R A) :
    Functor.Linear R (sourceFunctor (R := R) (A := A) Y) := sorry

/-- The target-variable derived Hom functor is additive. -/
@[stacks 0CS6 "additivity in the target variable of derived Hom"]
noncomputable instance targetFunctorAdditive (X : (K R A)ᵒᵖ) :
    (targetFunctor (R := R) (A := A) X).Additive := sorry

/-- The target-variable derived Hom functor is `R`-linear. -/
@[stacks 0CS6 "linearity in the target variable of derived Hom"]
noncomputable instance targetFunctorLinear (X : (K R A)ᵒᵖ) :
    Functor.Linear R (targetFunctor (R := R) (A := A) X) := sorry

/-- The source-variable derived Hom functor has the expected object formula. -/
@[simp, stacks 0CS6 "source-variable derived Hom object formula"]
theorem sourceFunctor_obj (X : (K R A)ᵒᵖ) (Y : K R A) :
    (sourceFunctor (R := R) (A := A) Y).obj X =
      DerivedCategory.Q.obj (homComplex X.unop.obj Y.obj) := sorry

/-- The target-variable derived Hom functor has the expected object formula. -/
@[simp, stacks 0CS6 "target-variable derived Hom object formula"]
theorem targetFunctor_obj (X : (K R A)ᵒᵖ) (Y : K R A) :
    (targetFunctor (R := R) (A := A) X).obj Y =
      DerivedCategory.Q.obj (homComplex X.unop.obj Y.obj) := sorry

/-- Source maps in the fixed-target derived Hom functor are the simultaneous Hom maps. -/
@[simp, stacks 0CS6 "source-variable derived Hom map formula"]
theorem sourceFunctor_map (Y : K R A) {X X' : (K R A)ᵒᵖ}
    (f : X ⟶ X') :
    (sourceFunctor (R := R) (A := A) Y).map f =
      mapHomotopy f.unop (𝟙 Y) := sorry

/-- Target maps in the fixed-source derived Hom functor are the simultaneous Hom maps. -/
@[simp, stacks 0CS6 "target-variable derived Hom map formula"]
theorem targetFunctor_map (X : (K R A)ᵒᵖ) {Y Y' : K R A}
    (g : Y ⟶ Y') :
    (targetFunctor (R := R) (A := A) X).map g =
      mapHomotopy (𝟙 X.unop) g := sorry

/-- The Hom bifunctor after applying a DG functor in both variables. -/
@[stacks 0CS6 "mapped derived Hom bifunctor"]
noncomputable abbrev mappedFunctor (F : DgFunctor R A B) :
    (K R A)ᵒᵖ × K R A ⥤ DerivedCategory (ModuleCat.{h} R) :=
  ((F.mapK).op.prod F.mapK) ⋙ functor (R := R) (A := B)

/-- Naturality of the Hom-complex map with respect to homotopy-category morphisms in both
variables. -/
theorem mapNatTrans_naturality (F : DgFunctor R A B)
    {X Y : (K R A)ᵒᵖ × K R A} (f : X ⟶ Y) :
    (functor (R := R) (A := A)).map f ≫
        DerivedCategory.Q.map (HomComplex.map F Y.1.unop.obj Y.2.obj) =
      DerivedCategory.Q.map (HomComplex.map F X.1.unop.obj X.2.obj) ≫
        (mappedFunctor F).map f := sorry

/-- A DG functor induces a natural transformation between the two Hom bifunctors before
derivation. -/
@[stacks 0CS6 "map of Hom bifunctors induced by a DG functor"]
noncomputable def mapNatTrans (F : DgFunctor R A B) :
    functor (R := R) (A := A) ⟶ mappedFunctor F where
  app X := DerivedCategory.Q.map (HomComplex.map F X.1.unop.obj X.2.obj)
  naturality _ _ f := mapNatTrans_naturality F f

variable {D : Type d} [Category.{e} D]

/-- Morphisms inverted when deriving both variables of an enriched Hom bifunctor. -/
@[stacks 0CS6 "product quasi-isomorphism property for derived Hom"]
abbrev qis (W : MorphismProperty (K R A)) :
    MorphismProperty ((K R A)ᵒᵖ × K R A) :=
  W.op.prod W

/-- The product localization used to pass both arguments of enriched Hom to derived objects. -/
@[stacks 0CS6 "product localization for derived Hom"]
abbrev localization (L : K R A ⥤ D) :
    (K R A)ᵒᵖ × K R A ⥤ Dᵒᵖ × D :=
  L.op.prod L

variable (L : K R A ⥤ D) (W : MorphismProperty (K R A))
variable [W.ContainsIdentities] [L.IsLocalization W]

namespace RHom

/-- The total right-derived enriched Hom bifunctor on arbitrary localized objects. -/
@[stacks 0CS6 "total derived Hom bifunctor of a DG category"]
noncomputable def functor
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    Dᵒᵖ × D ⥤ DerivedCategory (ModuleCat.{h} R) :=
  (Derived.functor (R := R) (A := A)).totalRightDerived (localization L) (qis W)

/-- The curried total derived Hom functor, with the localized source variable first. -/
@[stacks 0CS6 "curried total derived Hom functor"]
noncomputable def curried
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    Dᵒᵖ ⥤ D ⥤ DerivedCategory (ModuleCat.{h} R) :=
  Functor.curry.obj (functor L W)

/-- The total derived Hom functor with a fixed localized target. -/
@[stacks 0CS6 "source-variable total derived Hom functor"]
noncomputable def sourceFunctor (N : D)
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    Dᵒᵖ ⥤ DerivedCategory (ModuleCat.{h} R) :=
  (curried L W).flip.obj N

/-- The total derived Hom functor with a fixed localized source. -/
@[stacks 0CS6 "target-variable total derived Hom functor"]
noncomputable def targetFunctor (M : Dᵒᵖ)
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    D ⥤ DerivedCategory (ModuleCat.{h} R) :=
  (curried L W).obj M

/-- The fixed-target total derived Hom functor has the expected object formula. -/
@[simp, stacks 0CS6 "source-variable total derived Hom object formula"]
theorem sourceFunctor_obj (N : D) (M : Dᵒᵖ)
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    (sourceFunctor L W N).obj M = (functor L W).obj (M, N) := sorry

/-- The fixed-source total derived Hom functor has the expected object formula. -/
@[simp, stacks 0CS6 "target-variable total derived Hom object formula"]
theorem targetFunctor_obj (M : Dᵒᵖ) (N : D)
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    (targetFunctor L W M).obj N = (functor L W).obj (M, N) := sorry

/-- Source maps of total derived Hom are the first components of product maps. -/
@[simp, stacks 0CS6 "source-variable total derived Hom map formula"]
theorem sourceFunctor_map (N : D) {M M' : Dᵒᵖ} (f : M ⟶ M')
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    (sourceFunctor L W N).map f = (functor L W).map (f, 𝟙 N) := sorry

/-- Target maps of total derived Hom are the second components of product maps. -/
@[simp, stacks 0CS6 "target-variable total derived Hom map formula"]
theorem targetFunctor_map (M : Dᵒᵖ) {N N' : D} (g : N ⟶ N')
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    (targetFunctor L W M).map g = (functor L W).map (𝟙 M, g) := sorry

section SeparateVariables

section Additive

variable [Preadditive D] [L.Additive]

/-- Additivity of total derived Hom in the localized source variable. -/
@[stacks 0CS6 "additivity in the source variable of total derived Hom"]
noncomputable instance sourceFunctorAdditive (N : D)
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    (sourceFunctor L W N).Additive := sorry

/-- Additivity of total derived Hom in the localized target variable. -/
@[stacks 0CS6 "additivity in the target variable of total derived Hom"]
noncomputable instance targetFunctorAdditive (M : Dᵒᵖ)
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    (targetFunctor L W M).Additive := sorry

end Additive

section Linear

variable [Preadditive D] [Linear R D] [Functor.Linear R L]

/-- `R`-linearity of total derived Hom in the localized source variable. -/
@[stacks 0CS6 "linearity in the source variable of total derived Hom"]
noncomputable instance sourceFunctorLinear (N : D)
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    Functor.Linear R (sourceFunctor L W N) := sorry

/-- `R`-linearity of total derived Hom in the localized target variable. -/
@[stacks 0CS6 "linearity in the target variable of total derived Hom"]
noncomputable instance targetFunctorLinear (M : Dᵒᵖ)
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    Functor.Linear R (targetFunctor L W M) := sorry

end Linear

end SeparateVariables

/-- The universal unit from the homotopy-level Hom bifunctor to its total right-derived
bifunctor. -/
@[stacks 0CS6 "unit from homotopy Hom to total derived Hom"]
noncomputable def unit
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    Derived.functor (R := R) (A := A) ⟶ localization L ⋙ functor L W :=
  (Derived.functor (R := R) (A := A)).totalRightDerivedUnit (localization L) (qis W)

/-- The canonical `RHom` functor together with `unit` satisfies the universal property of a
right-derived functor. -/
@[stacks 0CS6 "total derived Hom right-derived universal property"]
instance isRightDerived
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)] :
    (functor L W).IsRightDerivedFunctor (unit L W) (qis W) := sorry

/-- Transport the canonical derived-Hom unit to an isomorphic right-derived model. -/
@[stacks 0CS6 "transported derived Hom unit"]
noncomputable def unitOfIso
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)]
    (T : Dᵒᵖ × D ⥤ DerivedCategory (ModuleCat.{h} R))
    (e : functor L W ≅ T) :
    Derived.functor (R := R) (A := A) ⟶ localization L ⋙ T :=
  unit L W ≫ Functor.whiskerLeft (localization L) e.hom

/-- Any supplied simultaneous right-derived Hom model is canonically isomorphic to total
derived Hom. -/
@[stacks 0CS6 "uniqueness of total derived Hom model"]
noncomputable abbrev modelIso
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)]
    (T : Dᵒᵖ × D ⥤ DerivedCategory (ModuleCat.{h} R))
    (η : Derived.functor (R := R) (A := A) ⟶ localization L ⋙ T)
    [T.IsRightDerivedFunctor η (qis W)] :
    functor L W ≅ T :=
  (functor L W).rightDerivedUnique T (unit L W) η (qis W)

/-- Transporting the canonical unit along the canonical model isomorphism recovers the supplied
right-derived unit. -/
@[stacks 0CS6 "transported derived Hom unit compatibility"]
theorem unitOfIso_modelIso
    [(Derived.functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)]
    (T : Dᵒᵖ × D ⥤ DerivedCategory (ModuleCat.{h} R))
    (η : Derived.functor (R := R) (A := A) ⟶ localization L ⋙ T)
    [T.IsRightDerivedFunctor η (qis W)] :
    unitOfIso L W T (modelIso L W T η) = η := sorry

end RHom

namespace RightDerivedMap

/-- The total right-derived functor of the Hom bifunctor obtained after applying a DG functor in
both variables. This is deliberately distinct from `RHom` composed with a left-derived functor. -/
@[stacks 0CS6 "right-derived Hom after a DG functor"]
noncomputable def target (F : DgFunctor R A B)
    [(mappedFunctor F).HasRightDerivedFunctor (qis W)] :
    Dᵒᵖ × D ⥤ DerivedCategory (ModuleCat.{h} R) :=
  (mappedFunctor F).totalRightDerived (localization L) (qis W)

/-- The universal unit from the mapped Hom bifunctor to its total right-derived functor. -/
@[stacks 0CS6 "unit for right-derived mapped Hom"]
noncomputable def unit (F : DgFunctor R A B)
    [(mappedFunctor F).HasRightDerivedFunctor (qis W)] :
    mappedFunctor F ⟶ localization L ⋙ target L W F :=
  (mappedFunctor F).totalRightDerivedUnit (localization L) (qis W)

/-- The right-derived mapped Hom functor together with `unit` satisfies the expected universal
property. -/
@[stacks 0CS6 "right-derived mapped Hom universal property"]
instance isRightDerived (F : DgFunctor R A B)
    [(mappedFunctor F).HasRightDerivedFunctor (qis W)] :
    (target L W F).IsRightDerivedFunctor (unit L W F) (qis W) := sorry

/-- Right derivation carries the map of Hom bifunctors induced by an `R`-linear DG functor to a
natural transformation. Its target is `target L W F`, not in general `RHom` after a left-derived
functor of `F`. -/
@[stacks 0CS6 "comparison of right-derived mapped Hom with RHom"]
noncomputable def comparison (F : DgFunctor R A B)
    [(functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)]
    [(mappedFunctor F).HasRightDerivedFunctor (qis W)] :
    RHom.functor L W ⟶ target L W F :=
  Functor.rightDerivedNatTrans (RHom.functor L W) (target L W F)
    (RHom.unit L W) (unit L W F) (qis W) (mapNatTrans F)

/-- The right-derived mapped-Hom comparison evaluated on arbitrary localized objects. -/
@[stacks 0CS6 "objectwise right-derived mapped-Hom comparison"]
noncomputable def comparisonApp (F : DgFunctor R A B)
    [(functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)]
    [(mappedFunctor F).HasRightDerivedFunctor (qis W)] (M N : D) :
    (RHom.functor L W).obj (Opposite.op M, N) ⟶
      (target L W F).obj (Opposite.op M, N) :=
  (comparison L W F).app (Opposite.op M, N)

/-- The comparison is uniquely characterized by its universal square before localization. -/
@[stacks 0CS6 "right-derived mapped-Hom comparison square"]
theorem comparison_fac (F : DgFunctor R A B)
    [(functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)]
    [(mappedFunctor F).HasRightDerivedFunctor (qis W)] :
    RHom.unit L W ≫ Functor.whiskerLeft (localization L) (comparison L W F) =
      mapNatTrans F ≫ unit L W F := sorry

/-- Degree-`n` cohomology of the right-derived mapped-Hom comparison, evaluated on arbitrary
localized objects. -/
@[stacks 0CS6 "cohomology of the right-derived mapped-Hom comparison"]
noncomputable def cohomologyMap (F : DgFunctor R A B)
    [(functor (R := R) (A := A)).HasRightDerivedFunctor (qis W)]
    [(mappedFunctor F).HasRightDerivedFunctor (qis W)] (M N : D) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{h} R) n).obj
        ((RHom.functor L W).obj (Opposite.op M, N)) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{h} R) n).obj
        ((target L W F).obj (Opposite.op M, N)) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{h} R) n).map
    (comparisonApp L W F M N)

end RightDerivedMap

end DifferentialGradedCategory.HomComplex.Derived
