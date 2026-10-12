/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Graded.Bimodule.Category
public import ReasLib.Algebra.Module.Graded.Bimodule.InternalHom

/-!
# Maps on Graded Internal Hom

The graded internal Hom is contravariant in its bimodule source and covariant in its right
graded-module target.  This file constructs both actions degree by degree, extends them across
the finite direct sum of homogeneous maps, and then lifts them to canonical degree-zero maps
between the wrapped internal-Hom objects.
-/

@[expose] public section

noncomputable section

namespace GradedModule.InternalHom

open CategoryTheory
open scoped DirectSum

universe i u v w y z

variable {ι : Type i} [DecidableEq ι] [AddCommMonoid ι]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
variable {𝒝 : ι → Submodule R B} [GradedAlgebra 𝒝]

variable {N N' N'' : Bimodule.{i, y, w, v, u} 𝒜 𝒝}
variable {P P' P'' : Right.{i, z, w, u} 𝒝}

/-- Postcompose one degree-`k` map by a degree-zero target map. -/
def mapTargetComponent (f : Right.HomogeneousMap P P' 0) (k : ι) :
    Right.HomogeneousMap N.toRight P k →ₗ[R]
      Right.HomogeneousMap N.toRight P' k :=
  Right.HomogeneousMap.postcompZeroLinear f

/-- Postcomposition on the finite direct sum of all homogeneous map degrees. -/
def mapTargetHom (f : Right.HomogeneousMap P P' 0) :
    Right.Hom N.toRight P →ₗ[R] Right.Hom N.toRight P' :=
  Right.Hom.postcompZero f

/-- Postcomposition lifted to the instance-safe internal-Hom wrappers. -/
def mapTargetLinear (f : Right.HomogeneousMap P P' 0) :
    InternalHom N P →ₗ[Aᵐᵒᵖ] InternalHom N P' where
  toFun g := ofHom (mapTargetHom (N := N) f g.toHom)
  map_add' := sorry
  map_smul' := sorry

/-- The covariant action of a degree-zero target map on graded internal-Hom objects. -/
@[stacks 09LN "covariance of graded relative internal Hom in the target"]
def mapTarget (f : Right.HomogeneousMap P P' 0) :
    Right.HomogeneousMap (obj N P) (obj N P') 0 :=
  ⟨mapTargetLinear (N := N) f, sorry⟩

/-- Precompose one degree-`k` map by a degree-zero bimodule morphism. -/
def mapSourceComponent (f : Bimodule.Hom N N') (k : ι) :
    Right.HomogeneousMap N'.toRight P k →ₗ[R]
      Right.HomogeneousMap N.toRight P k :=
  Right.HomogeneousMap.precompZeroLinear (Bimodule.Hom.toRightHom f)

/-- Precomposition on the finite direct sum of all homogeneous map degrees. -/
def mapSourceHom (f : Bimodule.Hom N N') :
    Right.Hom N'.toRight P →ₗ[R] Right.Hom N.toRight P :=
  Right.Hom.precompZero (Bimodule.Hom.toRightHom f)

/-- Precomposition lifted to the instance-safe internal-Hom wrappers. -/
def mapSourceLinear (f : Bimodule.Hom N N') :
    InternalHom N' P →ₗ[Aᵐᵒᵖ] InternalHom N P where
  toFun g := ofHom (mapSourceHom (P := P) f g.toHom)
  map_add' := sorry
  map_smul' := sorry

/-- The contravariant action of a degree-zero bimodule morphism on graded internal-Hom objects. -/
@[stacks 09LN "contravariance of graded relative internal Hom in the source"]
def mapSource (f : Bimodule.Hom N N') :
    Right.HomogeneousMap (obj N' P) (obj N P) 0 :=
  ⟨mapSourceLinear (P := P) f, sorry⟩

/-- Simultaneous source precomposition and target postcomposition on graded internal Hom. -/
@[stacks 09LN "functoriality of graded relative internal Hom"]
def map (f : Bimodule.Hom N N') (g : Right.HomogeneousMap P P' 0) :
    Right.HomogeneousMap (obj N' P) (obj N P') 0 :=
  Right.HomogeneousMap.compZero (mapTarget (N := N) g) (mapSource (P := P) f)

/-- Target postcomposition on one homogeneous component evaluates by ordinary composition. -/
@[simp]
theorem mapTargetComponent_apply (f : Right.HomogeneousMap P P' 0) (k : ι)
    (g : Right.HomogeneousMap N.toRight P k) (n : N) :
    (mapTargetComponent (N := N) f k g).1 n = f.1 (g.1 n) := sorry

/-- Source precomposition on one homogeneous component evaluates by ordinary composition. -/
@[simp]
theorem mapSourceComponent_apply (f : Bimodule.Hom N N') (k : ι)
    (g : Right.HomogeneousMap N'.toRight P k) (n : N) :
    (mapSourceComponent (P := P) f k g).1 n =
      g.1 (Bimodule.Hom.toLinearMap f n) := sorry

/-- Target postcomposition on total graded Hom evaluates after forgetting the direct sum. -/
@[simp]
theorem mapTargetHom_apply (f : Right.HomogeneousMap P P' 0)
    (g : Right.Hom N.toRight P) (n : N) :
    Right.Hom.toLinearMap N.toRight P' (mapTargetHom (N := N) f g) n =
      f.1 (Right.Hom.toLinearMap N.toRight P g n) := sorry

/-- Source precomposition on total graded Hom evaluates after forgetting the direct sum. -/
@[simp]
theorem mapSourceHom_apply (f : Bimodule.Hom N N')
    (g : Right.Hom N'.toRight P) (n : N) :
    Right.Hom.toLinearMap N.toRight P (mapSourceHom (P := P) f g) n =
      Right.Hom.toLinearMap N'.toRight P g (Bimodule.Hom.toLinearMap f n) := sorry

/-- The target action on internal-Hom objects is pointwise postcomposition. -/
@[simp]
theorem mapTarget_apply (f : Right.HomogeneousMap P P' 0)
    (g : InternalHom N P) (n : N) :
    toLinearMap N P' ((mapTarget (N := N) f).1 g) n = f.1 (g n) := sorry

/-- The source action on internal-Hom objects is pointwise precomposition. -/
@[simp]
theorem mapSource_apply (f : Bimodule.Hom N N')
    (g : InternalHom N' P) (n : N) :
    toLinearMap N P ((mapSource (P := P) f).1 g) n =
      g (Bimodule.Hom.toLinearMap f n) := sorry

/-- The simultaneous action evaluates by precomposition followed by postcomposition. -/
@[simp]
theorem map_apply (f : Bimodule.Hom N N') (g : Right.HomogeneousMap P P' 0)
    (h : InternalHom N' P) (n : N) :
    toLinearMap N P' ((map f g).1 h) n =
      g.1 (h (Bimodule.Hom.toLinearMap f n)) := sorry

/-- Postcomposition by the degree-zero identity is the identity internal-Hom map. -/
@[simp]
theorem mapTarget_id (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) :
    mapTarget (N := N) (Right.HomogeneousMap.id P) =
      Right.HomogeneousMap.id (obj N P) := sorry

/-- Target postcomposition preserves composition of degree-zero maps. -/
theorem mapTarget_comp (f : Right.HomogeneousMap P P' 0)
    (g : Right.HomogeneousMap P' P'' 0) :
    mapTarget (N := N) (Right.HomogeneousMap.compZero g f) =
      Right.HomogeneousMap.compZero (mapTarget (N := N) g) (mapTarget (N := N) f) := sorry

/-- Precomposition by the identity bimodule morphism is the identity internal-Hom map. -/
@[simp]
theorem mapSource_id (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) :
    mapSource (P := P) (Bimodule.Hom.id N) =
      Right.HomogeneousMap.id (obj N P) := sorry

/-- Source precomposition reverses composition of bimodule morphisms. -/
theorem mapSource_comp (f : Bimodule.Hom N N') (g : Bimodule.Hom N' N'') :
    mapSource (P := P) (Bimodule.Hom.comp g f) =
      Right.HomogeneousMap.compZero (mapSource (P := P) f) (mapSource (P := P) g) := sorry

/-- Source precomposition commutes with target postcomposition. -/
theorem map_interchange (f : Bimodule.Hom N N')
    (g : Right.HomogeneousMap P P' 0) :
    Right.HomogeneousMap.compZero (mapSource (P := P') f) (mapTarget (N := N') g) =
      Right.HomogeneousMap.compZero (mapTarget (N := N) g) (mapSource (P := P) f) := sorry

/-- The simultaneous internal-Hom action sends identities to the identity. -/
@[simp]
theorem map_id (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : Right.{i, z, w, u} 𝒝) :
    map (Bimodule.Hom.id N) (Right.HomogeneousMap.id P) =
      Right.HomogeneousMap.id (obj N P) := sorry

/-- Composition for the simultaneous contravariant-covariant internal-Hom action. -/
theorem map_comp (f : Bimodule.Hom N N') (f' : Bimodule.Hom N' N'')
    (g : Right.HomogeneousMap P P' 0) (g' : Right.HomogeneousMap P' P'' 0) :
    map (Bimodule.Hom.comp f' f) (Right.HomogeneousMap.compZero g' g) =
      Right.HomogeneousMap.compZero (map f g') (map f' g) := sorry

namespace DegreeZero

/-- Fixed-source graded internal Hom as a functor between the canonical degree-zero categories
of right graded modules. -/
@[stacks 09LN "fixed-bimodule graded internal Hom functor"]
def functor (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    CategoryTheory.GradedCategory.DegreeZero (R := R)
        (Right.{i, max i (max y z), w, u} 𝒝) ι ⥤
      CategoryTheory.GradedCategory.DegreeZero (R := R)
        (Right.{i, max i (max y z), v, u} 𝒜) ι where
  obj P := ⟨InternalHom.obj N P.obj⟩
  map {P P'} f :=
    Right.degreeZeroHomEquiv (InternalHom.obj N P.obj) (InternalHom.obj N P'.obj)
      (InternalHom.mapTarget (N := N)
        ((Right.degreeZeroHomEquiv P.obj P'.obj).symm f))
  map_id := sorry
  map_comp := sorry

/-- The fixed-source internal-Hom functor has the canonical graded internal-Hom object at every
right graded module. -/
@[simp]
theorem functor_obj_obj (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max y z), w, u} 𝒝) ι) :
    ((functor.{i, u, v, w, y, z} N).obj P).obj =
      InternalHom.obj N P.obj := sorry

/-- The fixed-source internal-Hom functor maps a degree-zero morphism by canonical
postcomposition. -/
@[simp]
theorem functor_map (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    {P P' : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max y z), w, u} 𝒝) ι}
    (f : P ⟶ P') :
    (functor.{i, u, v, w, y, z} N).map f =
      Right.degreeZeroHomEquiv (InternalHom.obj N P.obj) (InternalHom.obj N P'.obj)
        (InternalHom.mapTarget (N := N)
          ((Right.degreeZeroHomEquiv P.obj P'.obj).symm f)) := sorry

/-- Fixed-source graded internal Hom is additive on degree-zero morphisms. -/
instance functorAdditive (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    (functor.{i, u, v, w, y, z} N).Additive := sorry

/-- Fixed-source graded internal Hom is `R`-linear on degree-zero morphisms. -/
instance functorLinear (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    Functor.Linear R (functor.{i, u, v, w, y, z} N) := sorry

/-- A graded bimodule morphism induces a contravariant natural transformation between the
corresponding fixed-source internal-Hom functors. -/
@[stacks 09LN "naturality of graded internal Hom in the bimodule"]
def map (f : N ⟶ N') :
    functor.{i, u, v, w, y, z} N' ⟶ functor.{i, u, v, w, y, z} N where
  app P :=
    Right.degreeZeroHomEquiv (InternalHom.obj N' P.obj) (InternalHom.obj N P.obj)
      (InternalHom.mapSource (P := P.obj) f)
  naturality := sorry

/-- A component of bimodule precomposition is the canonical source map on graded internal
Hom. -/
@[simp]
theorem map_app (f : N ⟶ N')
    (P : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max y z), w, u} 𝒝) ι) :
    (map.{i, u, v, w, y, z} f).app P =
      Right.degreeZeroHomEquiv (InternalHom.obj N' P.obj) (InternalHom.obj N P.obj)
        (InternalHom.mapSource (P := P.obj) f) := sorry

/-- The identity graded bimodule morphism induces the identity internal-Hom transformation. -/
@[simp]
theorem map_id (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    map.{i, u, v, w, y, z} (𝟙 N) = 𝟙 (functor.{i, u, v, w, y, z} N) := sorry

/-- Internal-Hom transformations reverse composition of graded bimodule morphisms. -/
@[simp]
theorem map_comp (f : N ⟶ N') (g : N' ⟶ N'') :
    map.{i, u, v, w, y, z} (f ≫ g) =
      map.{i, u, v, w, y, z} g ≫ map.{i, u, v, w, y, z} f := sorry

/-- Graded internal Hom as a contravariant functor of its bimodule source, valued in functors
between the canonical degree-zero graded-module categories. -/
@[stacks 09LN "graded internal Hom as a functor of the bimodule"]
def bimoduleFunctor :
    (Bimodule.{i, y, w, v, u} 𝒜 𝒝)ᵒᵖ ⥤
      (CategoryTheory.GradedCategory.DegreeZero (R := R)
          (Right.{i, max i (max y z), w, u} 𝒝) ι ⥤
        CategoryTheory.GradedCategory.DegreeZero (R := R)
          (Right.{i, max i (max y z), v, u} 𝒜) ι) where
  obj N := functor.{i, u, v, w, y, z} N.unop
  map f := map.{i, u, v, w, y, z} f.unop
  map_id := sorry
  map_comp := sorry

/-- Evaluating the bimodule-parameter internal-Hom functor gives the fixed-source internal-Hom
functor. -/
@[simp]
theorem bimoduleFunctor_obj (N : (Bimodule.{i, y, w, v, u} 𝒜 𝒝)ᵒᵖ) :
    (bimoduleFunctor.{i, u, v, w, y, z} (𝒜 := 𝒜) (𝒝 := 𝒝)).obj N =
      functor.{i, u, v, w, y, z} N.unop := sorry

/-- The bimodule-parameter internal-Hom functor maps an opposite morphism to canonical source
precomposition. -/
@[simp]
theorem bimoduleFunctor_map
    {N N' : (Bimodule.{i, y, w, v, u} 𝒜 𝒝)ᵒᵖ} (f : N ⟶ N') :
    (bimoduleFunctor.{i, u, v, w, y, z} (𝒜 := 𝒜) (𝒝 := 𝒝)).map f =
      map.{i, u, v, w, y, z} f.unop := sorry

end DegreeZero

end GradedModule.InternalHom
