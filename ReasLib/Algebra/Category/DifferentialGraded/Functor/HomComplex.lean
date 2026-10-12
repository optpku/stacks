/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import ReasLib.CategoryTheory.Linear.Opposite
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Endomorphism
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Composition
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy

/-!
# Enriched Hom-complex functoriality

This file owns precomposition, postcomposition, the enriched Hom bifunctor, and the concrete
cochain map induced by a differential graded functor. Cohomology and derived-category images live
in separate leaves, so chain-level consumers do not import localization or representative-choice
machinery.
-/

@[expose] public section

noncomputable section

universe u v w h z

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedCategory.HomComplex

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w}
variable [DA : DifferentialGradedCategory.{u, v, h} R A]
variable [DB : DifferentialGradedCategory.{u, w, h} R B]

/-- Precomposition by a closed degree-zero morphism as a linear map in one degree of the
enriched Hom complex. -/
def precompLinear {X X' Y : A} (f : CompHom X' X) (n : ℤ) :
    (X ⟶[n] Y) →ₗ[R] (X' ⟶[n] Y) where
  toFun g := castHom (zero_add n) (DA.comp g f.val)
  map_add' := sorry
  map_smul' := sorry

/-- Degreewise precomposition evaluates by composition in the differential graded category. -/
@[simp]
theorem precompLinear_apply {X X' Y : A} (f : CompHom X' X) (n : ℤ)
    (g : X ⟶[n] Y) :
    precompLinear f n g = castHom (zero_add n) (DA.comp g f.val) := sorry

/-- Precomposition by a closed degree-zero morphism as a morphism of enriched Hom complexes. -/
def precomp {X X' Y : A} (f : CompHom X' X) :
    homComplex X Y ⟶ homComplex X' Y where
  f n := ModuleCat.ofHom (precompLinear f n)
  comm' := sorry

/-- The degree-`n` component of precomposition is its degreewise linear map. -/
@[simp]
theorem precomp_f {X X' Y : A} (f : CompHom X' X) (n : ℤ) :
    (precomp (Y := Y) f).f n = ModuleCat.ofHom (precompLinear (Y := Y) f n) := sorry

/-- Postcomposition by a closed degree-zero morphism as a linear map in one degree of the
enriched Hom complex. -/
def postcompLinear {X Y Y' : A} (g : CompHom Y Y') (n : ℤ) :
    (X ⟶[n] Y) →ₗ[R] (X ⟶[n] Y') where
  toFun f := castHom (add_zero n) (DA.comp g.val f)
  map_add' := sorry
  map_smul' := sorry

/-- Degreewise postcomposition evaluates by composition in the differential graded category. -/
@[simp]
theorem postcompLinear_apply {X Y Y' : A} (g : CompHom Y Y') (n : ℤ)
    (f : X ⟶[n] Y) :
    postcompLinear g n f = castHom (add_zero n) (DA.comp g.val f) := sorry

/-- Postcomposition by a closed degree-zero morphism as a morphism of enriched Hom complexes. -/
def postcomp {X Y Y' : A} (g : CompHom Y Y') :
    homComplex X Y ⟶ homComplex X Y' where
  f n := ModuleCat.ofHom (postcompLinear g n)
  comm' := sorry

/-- The degree-`n` component of postcomposition is its degreewise linear map. -/
@[simp]
theorem postcomp_f {X Y Y' : A} (g : CompHom Y Y') (n : ℤ) :
    (postcomp (X := X) g).f n = ModuleCat.ofHom (postcompLinear (X := X) g n) := sorry

/-- Precomposition by the identity closed morphism is the identity Hom-complex map. -/
@[simp]
theorem precomp_id (X Y : A) :
    precomp (Y := Y) (CompHom.id X) = 𝟙 (homComplex X Y) := sorry

/-- Postcomposition by the identity closed morphism is the identity Hom-complex map. -/
@[simp]
theorem postcomp_id (X Y : A) :
    postcomp (X := X) (CompHom.id Y) = 𝟙 (homComplex X Y) := sorry

/-- Successive precomposition maps compose contravariantly in the source. -/
theorem precomp_comp {X'' X' X Y : A}
    (f : CompHom X'' X') (g : CompHom X' X) :
    precomp (Y := Y) (CompHom.comp f g) = precomp g ≫ precomp f := sorry

/-- Successive postcomposition maps compose covariantly in the target. -/
theorem postcomp_comp {X Y Y' Y'' : A}
    (f : CompHom Y Y') (g : CompHom Y' Y'') :
    postcomp (X := X) (CompHom.comp f g) = postcomp f ≫ postcomp g := sorry

/-- Precomposition and postcomposition commute on enriched Hom complexes. -/
theorem precomp_postcomp {X' X Y Y' : A}
    (f : CompHom X' X) (g : CompHom Y Y') :
    precomp f ≫ postcomp g = postcomp g ≫ precomp f := sorry

/-- Enriched Hom complexes form a bifunctor, contravariant on the closed source category and
covariant on the closed target category. -/
@[stacks 0CS6 "enriched Hom-complex bifunctor"]
def bifunctor : (Comp R A)ᵒᵖ × Comp R A ⥤ CochainComplex (ModuleCat.{h} R) ℤ where
  obj X := homComplex X.1.unop.obj X.2.obj
  map f := precomp f.1.unop ≫ postcomp f.2
  map_id := sorry
  map_comp := sorry

/-- The curried enriched Hom-complex functor, with the source variable first. -/
@[stacks 0CS6 "curried enriched Hom-complex functor"]
noncomputable def curried : (Comp R A)ᵒᵖ ⥤ Comp R A ⥤ CochainComplex (ModuleCat.{h} R) ℤ :=
  Functor.curry.obj (bifunctor (R := R) (A := A))

/-- The enriched Hom-complex functor with a fixed target and varying source. -/
@[stacks 0CS6 "source-variable enriched Hom-complex functor"]
noncomputable def sourceFunctor (Y : Comp R A) :
    (Comp R A)ᵒᵖ ⥤ CochainComplex (ModuleCat.{h} R) ℤ :=
  (curried (R := R) (A := A)).flip.obj Y

/-- The enriched Hom-complex functor with a fixed source and varying target. -/
@[stacks 0CS6 "target-variable enriched Hom-complex functor"]
noncomputable def targetFunctor (X : (Comp R A)ᵒᵖ) :
    Comp R A ⥤ CochainComplex (ModuleCat.{h} R) ℤ :=
  (curried (R := R) (A := A)).obj X

/-- The source-variable enriched Hom-complex functor is additive. -/
@[stacks 0CS6 "additivity in the source variable of enriched Hom"]
noncomputable instance sourceFunctorAdditive (Y : Comp R A) :
    (sourceFunctor (R := R) (A := A) Y).Additive := sorry

/-- The source-variable enriched Hom-complex functor is `R`-linear. -/
@[stacks 0CS6 "linearity in the source variable of enriched Hom"]
noncomputable instance sourceFunctorLinear (Y : Comp R A) :
    Functor.Linear R (sourceFunctor (R := R) (A := A) Y) := sorry

/-- The target-variable enriched Hom-complex functor is additive. -/
@[stacks 0CS6 "additivity in the target variable of enriched Hom"]
noncomputable instance targetFunctorAdditive (X : (Comp R A)ᵒᵖ) :
    (targetFunctor (R := R) (A := A) X).Additive := sorry

/-- The target-variable enriched Hom-complex functor is `R`-linear. -/
@[stacks 0CS6 "linearity in the target variable of enriched Hom"]
noncomputable instance targetFunctorLinear (X : (Comp R A)ᵒᵖ) :
    Functor.Linear R (targetFunctor (R := R) (A := A) X) := sorry

/-- The source-variable functor evaluates to the expected Hom-complex. -/
@[simp, stacks 0CS6 "source-variable Hom-complex object formula"]
theorem sourceFunctor_obj (X : (Comp R A)ᵒᵖ) (Y : Comp R A) :
    (sourceFunctor (R := R) (A := A) Y).obj X = homComplex X.unop.obj Y.obj := sorry

/-- The target-variable functor evaluates to the expected Hom-complex. -/
@[simp, stacks 0CS6 "target-variable Hom-complex object formula"]
theorem targetFunctor_obj (X : (Comp R A)ᵒᵖ) (Y : Comp R A) :
    (targetFunctor (R := R) (A := A) X).obj Y = homComplex X.unop.obj Y.obj := sorry

/-- Source maps in the fixed-target Hom-complex functor are precomposition maps. -/
@[simp, stacks 0CS6 "source-variable Hom-complex map formula"]
theorem sourceFunctor_map (Y : Comp R A) {X X' : (Comp R A)ᵒᵖ}
    (f : X ⟶ X') :
    (sourceFunctor (R := R) (A := A) Y).map f = precomp f.unop := sorry

/-- Target maps in the fixed-source Hom-complex functor are postcomposition maps. -/
@[simp, stacks 0CS6 "target-variable Hom-complex map formula"]
theorem targetFunctor_map (X : (Comp R A)ᵒᵖ) {Y Y' : Comp R A}
    (g : Y ⟶ Y') :
    (targetFunctor (R := R) (A := A) X).map g = postcomp g := sorry

/-- The explicit cochain map on enriched Hom complexes induced by a differential graded
functor. -/
@[stacks 0CS6 "DG functor map on enriched Hom complexes"]
def map (F : DgFunctor R A B) (X Y : A) :
    homComplex X Y ⟶ homComplex (F.obj X) (F.obj Y) where
  f n := ModuleCat.ofHom (F.mapLinear n)
  comm' := sorry

/-- The degree-`n` component of the Hom-complex map is the linearized homogeneous action of the
DG functor. -/
@[simp]
theorem map_f (F : DgFunctor R A B) (X Y : A) (n : ℤ) :
    (map F X Y).f n = ModuleCat.ofHom (F.mapLinear n) := sorry

/-- The Hom-complex map is contravariantly natural in its source. -/
theorem map_naturality_source (F : DgFunctor R A B)
    {X X' Y : A} (f : CompHom X' X) :
    precomp f ≫ map F X' Y =
      map F X Y ≫ precomp (F.mapCompHom f) := sorry

/-- The Hom-complex map is covariantly natural in its target. -/
theorem map_naturality_target (F : DgFunctor R A B)
    {X Y Y' : A} (g : CompHom Y Y') :
    postcomp g ≫ map F X Y' =
      map F X Y ≫ postcomp (F.mapCompHom g) := sorry

/-- The enriched Hom-complex map of the identity DG functor is the identity map. -/
@[simp, stacks 0CS6 "identity law for DG functor maps on enriched Hom"]
theorem map_id (X Y : A) :
    map (DgFunctor.id R A) X Y = 𝟙 (homComplex X Y) := sorry

/-- Enriched Hom-complex maps compose in the same order as DG functors. -/
@[stacks 0CS6 "composition law for DG functor maps on enriched Hom"]
theorem map_comp {C : Type z} [DC : DifferentialGradedCategory.{u, z, h} R C]
    (G : DgFunctor R B C) (F : DgFunctor R A B) (X Y : A) :
    map (DgFunctor.comp G F) X Y =
      map F X Y ≫ map G (F.obj X) (F.obj Y) := sorry

/-- The enriched Hom-complex bifunctor after applying a DG functor in both variables. -/
@[stacks 0CS6 "mapped enriched Hom-complex bifunctor"]
noncomputable abbrev mappedBifunctor (F : DgFunctor R A B) :
    (Comp R A)ᵒᵖ × Comp R A ⥤ CochainComplex (ModuleCat.{h} R) ℤ :=
  ((F.mapComp).op.prod F.mapComp) ⋙ bifunctor (R := R) (A := B)

/-- The mapped enriched Hom-complex bifunctor has the expected object formula. -/
@[simp, stacks 0CS6 "mapped enriched Hom-complex object formula"]
theorem mappedBifunctor_obj (F : DgFunctor R A B)
    (X : (Comp R A)ᵒᵖ × Comp R A) :
    (mappedBifunctor F).obj X =
      homComplex (F.obj X.1.unop.obj) (F.obj X.2.obj) := sorry

/-- The pointwise DG Hom maps are jointly natural in the source and target variables. -/
theorem mapNatTrans_naturality (F : DgFunctor R A B)
    {X Y : (Comp R A)ᵒᵖ × Comp R A} (f : X ⟶ Y) :
    (bifunctor (R := R) (A := A)).map f ≫
        map F Y.1.unop.obj Y.2.obj =
      map F X.1.unop.obj X.2.obj ≫ (mappedBifunctor F).map f := sorry

/-- A DG functor induces a natural transformation of enriched Hom-complex bifunctors. -/
@[stacks 0CS6 "natural transformation of enriched Hom-complex bifunctors"]
noncomputable def mapNatTrans (F : DgFunctor R A B) :
    bifunctor (R := R) (A := A) ⟶ mappedBifunctor F where
  app X := map F X.1.unop.obj X.2.obj
  naturality _ _ f := mapNatTrans_naturality F f

/-- The component of `mapNatTrans` is the explicit DG Hom-complex map. -/
@[simp]
theorem mapNatTrans_app (F : DgFunctor R A B)
    (X : (Comp R A)ᵒᵖ × Comp R A) :
    (mapNatTrans F).app X = map F X.1.unop.obj X.2.obj := sorry

/-- Apply a DG functor to an enriched Hom complex, then postcompose with a closed morphism
from the image of its target. -/
@[stacks 0CS6 "DG functor map followed by enriched postcomposition"]
def mapPostcomp (F : DgFunctor R A B) (X Y : A) {Z : B}
    (g : CompHom (F.obj Y) Z) :
    homComplex X Y ⟶ homComplex (F.obj X) Z :=
  map F X Y ≫ postcomp g

/-- The map obtained by applying a DG functor and postcomposing is contravariantly natural in
the source. -/
theorem mapPostcomp_naturality_source (F : DgFunctor R A B)
    {X X' Y : A} {Z : B} (f : CompHom X' X)
    (g : CompHom (F.obj Y) Z) :
    precomp f ≫ mapPostcomp F X' Y g =
      mapPostcomp F X Y g ≫ precomp (F.mapCompHom f) := sorry

/-- Moving a closed target morphism across a DG functor map composes it with the final
postcomposition morphism. -/
theorem mapPostcomp_naturality_target (F : DgFunctor R A B)
    {X Y Y' : A} {Z : B} (f : CompHom Y Y')
    (g : CompHom (F.obj Y') Z) :
    postcomp f ≫ mapPostcomp F X Y' g =
      mapPostcomp F X Y (CompHom.comp (F.mapCompHom f) g) := sorry

/-- Further postcomposition may be absorbed into the closed morphism defining
`mapPostcomp`. -/
theorem mapPostcomp_postcomp (F : DgFunctor R A B)
    (X Y : A) {Z Z' : B} (f : CompHom (F.obj Y) Z)
    (g : CompHom Z Z') :
    mapPostcomp F X Y f ≫ postcomp g =
      mapPostcomp F X Y (CompHom.comp f g) := sorry

end DifferentialGradedCategory.HomComplex
