/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Bimodule.RelativeTensor.Map
public import ReasLib.Algebra.Module.Graded.Bimodule.Forget
public import ReasLib.Algebra.Module.Graded.Bimodule.RelativeTensor

/-!
# Functorial Maps on Graded Relative Tensor Products

The concrete maps on relative tensor quotients preserve total degree when the input maps have
degree zero.  This file packages those maps directly as morphisms between the canonical graded
relative tensor objects and supplies their bifunctorial API.
-/

@[expose] public section

noncomputable section

namespace GradedModule.RelativeTensor

open CategoryTheory

universe i u v w x y

variable {ι : Type i} [DecidableEq ι] [AddCommMonoid ι]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]
variable {𝒝 : ι → Submodule R B} [GradedAlgebra 𝒝]

variable {M M' M'' : Right.{i, x, v, u} 𝒜}
variable {N N' N'' : Bimodule.{i, y, w, v, u} 𝒜 𝒝}

/-- A degree-zero map in the right-module factor induces a degree-zero map of graded relative
tensor products. -/
def mapLeft (f : Right.HomogeneousMap M M' 0) :
    Right.HomogeneousMap (obj M N) (obj M' N) 0 :=
  ⟨Module.Bimodule.RelativeTensor.mapLeft
      (R := R) (A := A) (B := B) (N := N) f.1,
    sorry⟩

/-- A graded bimodule morphism induces a degree-zero map in the second relative tensor factor. -/
def mapRight (f : Bimodule.Hom N N') :
    Right.HomogeneousMap (obj M N) (obj M N') 0 :=
  ⟨Module.Bimodule.RelativeTensor.mapRight
      (R := R) (A := A) (B := B) (M := M) (Bimodule.Hom.toOrdinary f),
    sorry⟩

/-- The degree-zero map on graded relative tensor products induced simultaneously in both
factors. -/
@[stacks 09LN "functoriality of graded relative tensor products"]
def map (f : Right.HomogeneousMap M M' 0) (g : Bimodule.Hom N N') :
    Right.HomogeneousMap (obj M N) (obj M' N') 0 :=
  Right.HomogeneousMap.compZero (mapRight (M := M') g) (mapLeft (N := N) f)

/-- Mapping the first graded relative tensor factor evaluates on pure tensors as expected. -/
@[simp]
theorem mapLeft_tmul (f : Right.HomogeneousMap M M' 0) (m : M) (n : N) :
    (mapLeft (N := N) f).1
        (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) =
      Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) (f.1 m) n := sorry

/-- Mapping the second graded relative tensor factor evaluates on pure tensors as expected. -/
@[simp]
theorem mapRight_tmul (f : Bimodule.Hom N N') (m : M) (n : N) :
    (mapRight (M := M) f).1
        (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) =
      Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m
        (Bimodule.Hom.toLinearMap f n) := sorry

/-- Mapping both graded relative tensor factors evaluates componentwise on pure tensors. -/
@[simp]
theorem map_tmul (f : Right.HomogeneousMap M M' 0) (g : Bimodule.Hom N N')
    (m : M) (n : N) :
    (map f g).1 (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) =
      Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) (f.1 m)
        (Bimodule.Hom.toLinearMap g n) := sorry

/-- The identity on the first factor induces the identity graded relative tensor map. -/
@[simp]
theorem mapLeft_id :
    mapLeft (N := N) (Right.HomogeneousMap.id M) =
      Right.HomogeneousMap.id (obj M N) := sorry

/-- The identity on the second factor induces the identity graded relative tensor map. -/
@[simp]
theorem mapRight_id :
    mapRight (M := M) (Bimodule.Hom.id N) =
      Right.HomogeneousMap.id (obj M N) := sorry

/-- Maps induced in the first graded relative tensor factor preserve composition. -/
theorem mapLeft_comp (f : Right.HomogeneousMap M M' 0)
    (g : Right.HomogeneousMap M' M'' 0) :
    mapLeft (N := N) (Right.HomogeneousMap.compZero g f) =
      Right.HomogeneousMap.compZero (mapLeft (N := N) g) (mapLeft (N := N) f) := sorry

/-- Maps induced in the second graded relative tensor factor preserve composition. -/
theorem mapRight_comp (f : Bimodule.Hom N N') (g : Bimodule.Hom N' N'') :
    mapRight (M := M) (Bimodule.Hom.comp g f) =
      Right.HomogeneousMap.compZero (mapRight (M := M) g) (mapRight (M := M) f) := sorry

/-- The maps induced in the two graded relative tensor factors commute. -/
theorem mapLeft_mapRight (f : Right.HomogeneousMap M M' 0) (g : Bimodule.Hom N N') :
    Right.HomogeneousMap.compZero (mapRight (M := M') g) (mapLeft (N := N) f) =
      Right.HomogeneousMap.compZero (mapLeft (N := N') f) (mapRight (M := M) g) := sorry

/-- The simultaneous graded relative tensor map can equivalently be formed in the opposite
factor order. -/
theorem map_eq_mapLeft_comp_mapRight
    (f : Right.HomogeneousMap M M' 0) (g : Bimodule.Hom N N') :
    map f g =
      Right.HomogeneousMap.compZero (mapLeft (N := N') f) (mapRight (M := M) g) := sorry

/-- Mapping both factors by identities is the identity graded relative tensor map. -/
@[simp]
theorem map_id :
    map (Right.HomogeneousMap.id M) (Bimodule.Hom.id N) =
      Right.HomogeneousMap.id (obj M N) := sorry

/-- The simultaneous map with the identity in the first factor is `mapRight`. -/
@[simp]
theorem map_id_left (g : Bimodule.Hom N N') :
    map (Right.HomogeneousMap.id M) g = mapRight (M := M) g := sorry

/-- The simultaneous map with the identity in the second factor is `mapLeft`. -/
@[simp]
theorem map_id_right (f : Right.HomogeneousMap M M' 0) :
    map f (Bimodule.Hom.id N) = mapLeft (N := N) f := sorry

/-- Simultaneous graded relative tensor maps preserve composition in both variables. -/
theorem map_comp (f : Right.HomogeneousMap M M' 0)
    (f' : Right.HomogeneousMap M' M'' 0) (g : Bimodule.Hom N N')
    (g' : Bimodule.Hom N' N'') :
    map (Right.HomogeneousMap.compZero f' f) (Bimodule.Hom.comp g' g) =
      Right.HomogeneousMap.compZero (map f' g') (map f g) := sorry

namespace DegreeZero

/-- Tensoring with a fixed graded bimodule as a functor between the canonical degree-zero
categories of right graded modules. -/
@[stacks 09LN "fixed-bimodule graded relative tensor functor"]
def functor (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    CategoryTheory.GradedCategory.DegreeZero (R := R)
        (Right.{i, max i (max x y), v, u} 𝒜) ι ⥤
      CategoryTheory.GradedCategory.DegreeZero (R := R)
        (Right.{i, max i (max x y), w, u} 𝒝) ι where
  obj M := ⟨RelativeTensor.obj M.obj N⟩
  map {M M'} f :=
    Right.degreeZeroHomEquiv (RelativeTensor.obj M.obj N) (RelativeTensor.obj M'.obj N)
      (RelativeTensor.mapLeft (N := N)
        ((Right.degreeZeroHomEquiv M.obj M'.obj).symm f))
  map_id := sorry
  map_comp := sorry

/-- The fixed-bimodule tensor functor has the canonical graded relative tensor object at every
right graded module. -/
@[simp]
theorem functor_obj_obj (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι) :
    ((functor.{i, u, v, w, x, y} N).obj M).obj =
      RelativeTensor.obj M.obj N := sorry

/-- The fixed-bimodule tensor functor maps a degree-zero morphism by the canonical tensor map. -/
@[simp]
theorem functor_map (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    {M M' : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι}
    (f : M ⟶ M') :
    (functor.{i, u, v, w, x, y} N).map f =
      Right.degreeZeroHomEquiv (RelativeTensor.obj M.obj N) (RelativeTensor.obj M'.obj N)
        (RelativeTensor.mapLeft (N := N)
          ((Right.degreeZeroHomEquiv M.obj M'.obj).symm f)) := sorry

/-- Tensoring with a fixed graded bimodule is additive on degree-zero morphisms. -/
instance functorAdditive (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    (functor.{i, u, v, w, x, y} N).Additive := sorry

/-- Tensoring with a fixed graded bimodule is `R`-linear on degree-zero morphisms. -/
instance functorLinear (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    Functor.Linear R (functor.{i, u, v, w, x, y} N) := sorry

/-- A graded bimodule morphism induces a natural transformation between the corresponding
fixed-bimodule tensor functors. -/
@[stacks 09LN "naturality of graded relative tensor in the bimodule"]
def map (f : N ⟶ N') :
    functor.{i, u, v, w, x, y} N ⟶ functor.{i, u, v, w, x, y} N' where
  app M :=
    Right.degreeZeroHomEquiv (RelativeTensor.obj M.obj N) (RelativeTensor.obj M.obj N')
      (RelativeTensor.mapRight (M := M.obj) f)
  naturality := sorry

/-- A component of the natural transformation induced by a graded bimodule morphism is the
canonical map on the second relative tensor factor. -/
@[simp]
theorem map_app (f : N ⟶ N')
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι) :
    (map.{i, u, v, w, x, y} f).app M =
      Right.degreeZeroHomEquiv (RelativeTensor.obj M.obj N) (RelativeTensor.obj M.obj N')
        (RelativeTensor.mapRight (M := M.obj) f) := sorry

/-- The identity graded bimodule morphism induces the identity tensor transformation. -/
@[simp]
theorem map_id (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    map.{i, u, v, w, x, y} (𝟙 N) = 𝟙 (functor.{i, u, v, w, x, y} N) := sorry

/-- Tensor transformations preserve composition of graded bimodule morphisms. -/
@[simp]
theorem map_comp (f : N ⟶ N') (g : N' ⟶ N'') :
    map.{i, u, v, w, x, y} (f ≫ g) =
      map.{i, u, v, w, x, y} f ≫ map.{i, u, v, w, x, y} g := sorry

/-- Relative tensor product as a functor of the graded bimodule parameter, valued in functors
between the canonical degree-zero graded-module categories. -/
@[stacks 09LN "graded relative tensor as a functor of the bimodule"]
def bimoduleFunctor :
    Bimodule.{i, y, w, v, u} 𝒜 𝒝 ⥤
      (CategoryTheory.GradedCategory.DegreeZero (R := R)
          (Right.{i, max i (max x y), v, u} 𝒜) ι ⥤
        CategoryTheory.GradedCategory.DegreeZero (R := R)
          (Right.{i, max i (max x y), w, u} 𝒝) ι) where
  obj N := functor.{i, u, v, w, x, y} N
  map f := map.{i, u, v, w, x, y} f
  map_id := sorry
  map_comp := sorry

/-- Evaluating the bimodule-parameter tensor functor gives the fixed-bimodule tensor functor.
-/
@[simp]
theorem bimoduleFunctor_obj (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    (bimoduleFunctor.{i, u, v, w, x, y} (𝒜 := 𝒜) (𝒝 := 𝒝)).obj N =
      functor.{i, u, v, w, x, y} N := sorry

/-- The bimodule-parameter tensor functor maps a morphism to its canonical tensor natural
transformation. -/
@[simp]
theorem bimoduleFunctor_map {N N' : Bimodule.{i, y, w, v, u} 𝒜 𝒝} (f : N ⟶ N') :
    (bimoduleFunctor.{i, u, v, w, x, y} (𝒜 := 𝒜) (𝒝 := 𝒝)).map f =
      map.{i, u, v, w, x, y} f := sorry

end DegreeZero

end GradedModule.RelativeTensor
