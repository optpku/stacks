/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
  map_add' := by
    intro g h
    rw [DA.comp_add_left, castHom_add]
  map_smul' := by
    intro r g
    rw [DA.comp_smul_left, castHom_smul]
    rfl

/-- Degreewise precomposition evaluates by composition in the differential graded category. -/
@[simp]
theorem precompLinear_apply {X X' Y : A} (f : CompHom X' X) (n : ℤ)
    (g : X ⟶[n] Y) :
    precompLinear f n g = castHom (zero_add n) (DA.comp g f.val) := by rfl

/-- Precomposition by a closed degree-zero morphism as a morphism of enriched Hom complexes. -/
def precomp {X X' Y : A} (f : CompHom X' X) :
    homComplex X Y ⟶ homComplex X' Y where
  f n := ModuleCat.ofHom (precompLinear f n)
  comm' := by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    simp only [homComplex, CochainComplex.of_d]
    ext t
    change DA.d i (castHom (zero_add i) (DA.comp t f.val)) =
      castHom (zero_add (i + 1)) (DA.comp (DA.d i t) f.val)
    simp only [d_castHom, DA.d_comp, show DA.d 0 f.val = 0 from f.property,
      comp_zero_right, castHom_zero, smul_zero, add_zero, castHom_trans]

/-- The degree-`n` component of precomposition is its degreewise linear map. -/
@[simp]
theorem precomp_f {X X' Y : A} (f : CompHom X' X) (n : ℤ) :
    (precomp (Y := Y) f).f n = ModuleCat.ofHom (precompLinear (Y := Y) f n) := by rfl

/-- Postcomposition by a closed degree-zero morphism as a linear map in one degree of the
enriched Hom complex. -/
def postcompLinear {X Y Y' : A} (g : CompHom Y Y') (n : ℤ) :
    (X ⟶[n] Y) →ₗ[R] (X ⟶[n] Y') where
  toFun f := castHom (add_zero n) (DA.comp g.val f)
  map_add' := by
    intro f h
    rw [DA.comp_add_right, castHom_add]
  map_smul' := by
    intro r f
    rw [DA.comp_smul_right, castHom_smul]
    rfl

/-- Degreewise postcomposition evaluates by composition in the differential graded category. -/
@[simp]
theorem postcompLinear_apply {X Y Y' : A} (g : CompHom Y Y') (n : ℤ)
    (f : X ⟶[n] Y) :
    postcompLinear g n f = castHom (add_zero n) (DA.comp g.val f) := by rfl

/-- Postcomposition by a closed degree-zero morphism as a morphism of enriched Hom complexes. -/
def postcomp {X Y Y' : A} (g : CompHom Y Y') :
    homComplex X Y ⟶ homComplex X Y' where
  f n := ModuleCat.ofHom (postcompLinear g n)
  comm' := by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    simp only [homComplex, CochainComplex.of_d]
    ext t
    change DA.d i (castHom (add_zero i) (DA.comp g.val t)) =
      castHom (add_zero (i + 1)) (DA.comp g.val (DA.d i t))
    simp only [d_castHom, DA.d_comp, show DA.d 0 g.val = 0 from g.property,
      comp_zero_left, castHom_zero, zero_add, Int.negOnePow_zero, Units.val_one, Int.cast_one,
      one_smul, castHom_trans]

/-- The degree-`n` component of postcomposition is its degreewise linear map. -/
@[simp]
theorem postcomp_f {X Y Y' : A} (g : CompHom Y Y') (n : ℤ) :
    (postcomp (X := X) g).f n = ModuleCat.ofHom (postcompLinear (X := X) g n) := by rfl

/-- Precomposition by the identity closed morphism is the identity Hom-complex map. -/
@[simp]
theorem precomp_id (X Y : A) :
    precomp (Y := Y) (CompHom.id X) = 𝟙 (homComplex X Y) := by
  ext n t
  exact DA.comp_id_hom t

/-- Postcomposition by the identity closed morphism is the identity Hom-complex map. -/
@[simp]
theorem postcomp_id (X Y : A) :
    postcomp (X := X) (CompHom.id Y) = 𝟙 (homComplex X Y) := by
  ext n t
  exact DA.id_comp_hom t

/-- Successive precomposition maps compose contravariantly in the source. -/
theorem precomp_comp {X'' X' X Y : A}
    (f : CompHom X'' X') (g : CompHom X' X) :
    precomp (Y := Y) (CompHom.comp f g) = precomp g ≫ precomp f := by
  ext n t
  change castHom (zero_add n) (DA.comp t (DA.comp g.val f.val)) =
    castHom (zero_add n) (DA.comp (castHom (zero_add n) (DA.comp t g.val)) f.val)
  rw [← comp_castHom_left, ← DA.comp_assoc, castHom_trans, castHom_trans]
  rfl

/-- Successive postcomposition maps compose covariantly in the target. -/
theorem postcomp_comp {X Y Y' Y'' : A}
    (f : CompHom Y Y') (g : CompHom Y' Y'') :
    postcomp (X := X) (CompHom.comp f g) = postcomp f ≫ postcomp g := by
  ext n t
  change castHom (add_zero n) (DA.comp (DA.comp g.val f.val) t) =
    castHom (add_zero n) (DA.comp g.val (castHom (add_zero n) (DA.comp f.val t)))
  rw [← comp_castHom_right]
  erw [← DA.comp_assoc]
  simp only [castHom_trans]
  erw [castHom_trans]

/-- Precomposition and postcomposition commute on enriched Hom complexes. -/
theorem precomp_postcomp {X' X Y Y' : A}
    (f : CompHom X' X) (g : CompHom Y Y') :
    precomp f ≫ postcomp g = postcomp g ≫ precomp f := by
  ext n t
  change castHom (add_zero n) (DA.comp g.val (castHom (zero_add n) (DA.comp t f.val))) =
    castHom (zero_add n) (DA.comp (castHom (add_zero n) (DA.comp g.val t)) f.val)
  simpa only [← comp_castHom_right, ← comp_castHom_left, castHom_trans] using
    congrArg (castHom (show 0 + (n + 0) = n by simp)) (DA.comp_assoc g.val t f.val)

/-- Enriched Hom complexes form a bifunctor, contravariant on the closed source category and
covariant on the closed target category. -/
@[stacks 0CS6 "enriched Hom-complex bifunctor"]
def bifunctor : (Comp R A)ᵒᵖ × Comp R A ⥤ CochainComplex (ModuleCat.{h} R) ℤ where
  obj X := homComplex X.1.unop.obj X.2.obj
  map f := precomp f.1.unop ≫ postcomp f.2
  map_id := by
    intro X
    change precomp (CompHom.id X.1.unop.obj) ≫ postcomp (CompHom.id X.2.obj) = _
    rw [precomp_id, postcomp_id, Category.id_comp]
  map_comp := by
    intro X Y Z f g
    change precomp (CompHom.comp g.1.unop f.1.unop) ≫
      postcomp (CompHom.comp f.2 g.2) =
        (precomp f.1.unop ≫ postcomp f.2) ≫ (precomp g.1.unop ≫ postcomp g.2)
    rw [precomp_comp, postcomp_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (precomp g.1.unop) (postcomp f.2),
      precomp_postcomp, Category.assoc]

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
    (sourceFunctor (R := R) (A := A) Y).Additive := by
  constructor
  intro X X' f g
  change precomp (f + g).unop ≫ postcomp (CompHom.id Y.obj) =
    (precomp f.unop ≫ postcomp (CompHom.id Y.obj)) +
      (precomp g.unop ≫ postcomp (CompHom.id Y.obj))
  simp only [postcomp_id, Category.comp_id]
  ext n t
  change castHom (zero_add n) (DA.comp t (f.unop.val + g.unop.val)) =
    castHom (zero_add n) (DA.comp t f.unop.val) +
      castHom (zero_add n) (DA.comp t g.unop.val)
  rw [DA.comp_add_right, castHom_add]

/-- The source-variable enriched Hom-complex functor is `R`-linear. -/
@[stacks 0CS6 "linearity in the source variable of enriched Hom"]
noncomputable instance sourceFunctorLinear (Y : Comp R A) :
    Functor.Linear R (sourceFunctor (R := R) (A := A) Y) := by
  constructor
  intro X X' f r
  change precomp (r • f).unop ≫ postcomp (CompHom.id Y.obj) =
    r • (precomp f.unop ≫ postcomp (CompHom.id Y.obj))
  simp only [postcomp_id, Category.comp_id]
  ext n t
  change castHom (zero_add n) (DA.comp t (r • f.unop.val)) =
    r • castHom (zero_add n) (DA.comp t f.unop.val)
  rw [DA.comp_smul_right, castHom_smul]

/-- The target-variable enriched Hom-complex functor is additive. -/
@[stacks 0CS6 "additivity in the target variable of enriched Hom"]
noncomputable instance targetFunctorAdditive (X : (Comp R A)ᵒᵖ) :
    (targetFunctor (R := R) (A := A) X).Additive := by
  constructor
  intro Y Y' f g
  change precomp (CompHom.id X.unop.obj) ≫ postcomp (f + g) =
    (precomp (CompHom.id X.unop.obj) ≫ postcomp f) +
      (precomp (CompHom.id X.unop.obj) ≫ postcomp g)
  simp only [precomp_id, Category.id_comp]
  ext n t
  change castHom (add_zero n) (DA.comp (f.val + g.val) t) =
    castHom (add_zero n) (DA.comp f.val t) + castHom (add_zero n) (DA.comp g.val t)
  rw [DA.comp_add_left, castHom_add]

/-- The target-variable enriched Hom-complex functor is `R`-linear. -/
@[stacks 0CS6 "linearity in the target variable of enriched Hom"]
noncomputable instance targetFunctorLinear (X : (Comp R A)ᵒᵖ) :
    Functor.Linear R (targetFunctor (R := R) (A := A) X) := by
  constructor
  intro Y Y' f r
  change precomp (CompHom.id X.unop.obj) ≫ postcomp (r • f) =
    r • (precomp (CompHom.id X.unop.obj) ≫ postcomp f)
  simp only [precomp_id, Category.id_comp]
  ext n t
  change castHom (add_zero n) (DA.comp (r • f.val) t) =
    r • castHom (add_zero n) (DA.comp f.val t)
  rw [DA.comp_smul_left, castHom_smul]

/-- The source-variable functor evaluates to the expected Hom-complex. -/
@[simp, stacks 0CS6 "source-variable Hom-complex object formula"]
theorem sourceFunctor_obj (X : (Comp R A)ᵒᵖ) (Y : Comp R A) :
    (sourceFunctor (R := R) (A := A) Y).obj X = homComplex X.unop.obj Y.obj := by rfl

/-- The target-variable functor evaluates to the expected Hom-complex. -/
@[simp, stacks 0CS6 "target-variable Hom-complex object formula"]
theorem targetFunctor_obj (X : (Comp R A)ᵒᵖ) (Y : Comp R A) :
    (targetFunctor (R := R) (A := A) X).obj Y = homComplex X.unop.obj Y.obj := by rfl

/-- Source maps in the fixed-target Hom-complex functor are precomposition maps. -/
@[simp, stacks 0CS6 "source-variable Hom-complex map formula"]
theorem sourceFunctor_map (Y : Comp R A) {X X' : (Comp R A)ᵒᵖ}
    (f : X ⟶ X') :
    (sourceFunctor (R := R) (A := A) Y).map f = precomp f.unop := by
  change precomp f.unop ≫ postcomp (CompHom.id Y.obj) = _
  rw [postcomp_id, Category.comp_id]

/-- Target maps in the fixed-source Hom-complex functor are postcomposition maps. -/
@[simp, stacks 0CS6 "target-variable Hom-complex map formula"]
theorem targetFunctor_map (X : (Comp R A)ᵒᵖ) {Y Y' : Comp R A}
    (g : Y ⟶ Y') :
    (targetFunctor (R := R) (A := A) X).map g = postcomp g := by
  change precomp (CompHom.id X.unop.obj) ≫ postcomp g = _
  rw [precomp_id, Category.id_comp]

/-- The explicit cochain map on enriched Hom complexes induced by a differential graded
functor. -/
@[stacks 0CS6 "DG functor map on enriched Hom complexes"]
def map (F : DgFunctor R A B) (X Y : A) :
    homComplex X Y ⟶ homComplex (F.obj X) (F.obj Y) where
  f n := ModuleCat.ofHom (F.mapLinear n)
  comm' := by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    simp only [homComplex, CochainComplex.of_d]
    ext t
    exact (F.map_d t).symm

/-- The degree-`n` component of the Hom-complex map is the linearized homogeneous action of the
DG functor. -/
@[simp]
theorem map_f (F : DgFunctor R A B) (X Y : A) (n : ℤ) :
    (map F X Y).f n = ModuleCat.ofHom (F.mapLinear n) := by rfl

private theorem map_castHom (F : DgFunctor R A B) {X Y : A} {i j : ℤ}
    (hij : i = j) (f : X ⟶[i] Y) :
    F.map (castHom hij f) = castHom hij (F.map f) := by
  cases hij
  rfl

/-- The Hom-complex map is contravariantly natural in its source. -/
theorem map_naturality_source (F : DgFunctor R A B)
    {X X' Y : A} (f : CompHom X' X) :
    precomp f ≫ map F X' Y =
      map F X Y ≫ precomp (F.mapCompHom f) := by
  ext n t
  change F.map (castHom (zero_add n) (DA.comp t f.val)) =
    castHom (zero_add n) (DB.comp (F.map t) (F.map f.val))
  rw [map_castHom, F.map_comp]

/-- The Hom-complex map is covariantly natural in its target. -/
theorem map_naturality_target (F : DgFunctor R A B)
    {X Y Y' : A} (g : CompHom Y Y') :
    postcomp g ≫ map F X Y' =
      map F X Y ≫ postcomp (F.mapCompHom g) := by
  ext n t
  change F.map (castHom (add_zero n) (DA.comp g.val t)) =
    castHom (add_zero n) (DB.comp (F.map g.val) (F.map t))
  rw [map_castHom, F.map_comp]

/-- The enriched Hom-complex map of the identity DG functor is the identity map. -/
@[simp, stacks 0CS6 "identity law for DG functor maps on enriched Hom"]
theorem map_id (X Y : A) :
    map (DgFunctor.id R A) X Y = 𝟙 (homComplex X Y) := by
  ext n t
  rfl

/-- Enriched Hom-complex maps compose in the same order as DG functors. -/
@[stacks 0CS6 "composition law for DG functor maps on enriched Hom"]
theorem map_comp {C : Type z} [DC : DifferentialGradedCategory.{u, z, h} R C]
    (G : DgFunctor R B C) (F : DgFunctor R A B) (X Y : A) :
    map (DgFunctor.comp G F) X Y =
      map F X Y ≫ map G (F.obj X) (F.obj Y) := by
  ext n t
  rfl

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
      homComplex (F.obj X.1.unop.obj) (F.obj X.2.obj) := by rfl

/-- The pointwise DG Hom maps are jointly natural in the source and target variables. -/
theorem mapNatTrans_naturality (F : DgFunctor R A B)
    {X Y : (Comp R A)ᵒᵖ × Comp R A} (f : X ⟶ Y) :
    (bifunctor (R := R) (A := A)).map f ≫
        map F Y.1.unop.obj Y.2.obj =
      map F X.1.unop.obj X.2.obj ≫ (mappedBifunctor F).map f := by
  change (precomp f.1.unop ≫ postcomp f.2) ≫ map F Y.1.unop.obj Y.2.obj =
    map F X.1.unop.obj X.2.obj ≫
      (precomp (F.mapCompHom f.1.unop) ≫ postcomp (F.mapCompHom f.2))
  rw [Category.assoc, map_naturality_target, ← Category.assoc,
    map_naturality_source, Category.assoc]

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
    (mapNatTrans F).app X = map F X.1.unop.obj X.2.obj := by rfl

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
      mapPostcomp F X Y g ≫ precomp (F.mapCompHom f) := by
  unfold mapPostcomp
  rw [← Category.assoc, map_naturality_source, Category.assoc,
    precomp_postcomp, ← Category.assoc]

/-- Moving a closed target morphism across a DG functor map composes it with the final
postcomposition morphism. -/
theorem mapPostcomp_naturality_target (F : DgFunctor R A B)
    {X Y Y' : A} {Z : B} (f : CompHom Y Y')
    (g : CompHom (F.obj Y') Z) :
    postcomp f ≫ mapPostcomp F X Y' g =
      mapPostcomp F X Y (CompHom.comp (F.mapCompHom f) g) := by
  unfold mapPostcomp
  rw [← Category.assoc, map_naturality_target, Category.assoc, ← postcomp_comp]

/-- Further postcomposition may be absorbed into the closed morphism defining
`mapPostcomp`. -/
theorem mapPostcomp_postcomp (F : DgFunctor R A B)
    (X Y : A) {Z Z' : B} (f : CompHom (F.obj Y) Z)
    (g : CompHom Z Z') :
    mapPostcomp F X Y f ≫ postcomp g =
      mapPostcomp F X Y (CompHom.comp f g) := by
  simp only [mapPostcomp, postcomp_comp, Category.assoc]

end DifferentialGradedCategory.HomComplex
