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
    by
      intro k x hx
      change _ ∈ grading M' N (k + 0)
      rw [add_zero]
      have h : grading M N k ≤ Submodule.comap
          ((Module.Bimodule.RelativeTensor.mapLeft
            (R := R) (A := A) (B := B) (N := N) f.1).restrictScalars R)
          (grading M' N k) := by
        apply Submodule.span_le.mpr
        rintro z ⟨p, q, m, n, hm, hn, hpq, rfl⟩
        change Module.Bimodule.RelativeTensor.mapLeft
          (R := R) (A := A) (B := B) (N := N) f.1
            (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) ∈ grading M' N k
        rw [Module.Bimodule.RelativeTensor.mapLeft_tmul]
        apply Submodule.subset_span
        exact ⟨p, q, f.1 m, n, by simpa only [add_zero] using f.2 p m hm,
          hn, hpq, rfl⟩
      exact h hx⟩

/-- A graded bimodule morphism induces a degree-zero map in the second relative tensor factor. -/
def mapRight (f : Bimodule.Hom N N') :
    Right.HomogeneousMap (obj M N) (obj M N') 0 :=
  ⟨Module.Bimodule.RelativeTensor.mapRight
      (R := R) (A := A) (B := B) (M := M) (Bimodule.Hom.toOrdinary f),
    by
      intro k x hx
      change _ ∈ grading M N' (k + 0)
      rw [add_zero]
      have h : grading M N k ≤ Submodule.comap
          ((Module.Bimodule.RelativeTensor.mapRight
            (R := R) (A := A) (B := B) (M := M)
              (Bimodule.Hom.toOrdinary f)).restrictScalars R)
          (grading M N' k) := by
        apply Submodule.span_le.mpr
        rintro z ⟨p, q, m, n, hm, hn, hpq, rfl⟩
        change Module.Bimodule.RelativeTensor.mapRight
          (R := R) (A := A) (B := B) (M := M) (Bimodule.Hom.toOrdinary f)
            (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) ∈ grading M N' k
        rw [Module.Bimodule.RelativeTensor.mapRight_tmul]
        apply Submodule.subset_span
        exact ⟨p, q, m, Bimodule.Hom.toLinearMap f n, hm,
          Bimodule.Hom.map_mem f hn, hpq, rfl⟩
      exact h hx⟩

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
      Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) (f.1 m) n := by
  exact Module.Bimodule.RelativeTensor.mapLeft_tmul f.1 m n

/-- Mapping the second graded relative tensor factor evaluates on pure tensors as expected. -/
@[simp]
theorem mapRight_tmul (f : Bimodule.Hom N N') (m : M) (n : N) :
    (mapRight (M := M) f).1
        (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) =
      Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m
        (Bimodule.Hom.toLinearMap f n) := by
  exact Module.Bimodule.RelativeTensor.mapRight_tmul (Bimodule.Hom.toOrdinary f) m n

/-- Mapping both graded relative tensor factors evaluates componentwise on pure tensors. -/
@[simp]
theorem map_tmul (f : Right.HomogeneousMap M M' 0) (g : Bimodule.Hom N N')
    (m : M) (n : N) :
    (map f g).1 (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) =
      Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) (f.1 m)
        (Bimodule.Hom.toLinearMap g n) := by
  simp only [map, Right.HomogeneousMap.compZero_apply, mapLeft_tmul, mapRight_tmul]

/-- The identity on the first factor induces the identity graded relative tensor map. -/
@[simp]
theorem mapLeft_id :
    mapLeft (N := N) (Right.HomogeneousMap.id M) =
      Right.HomogeneousMap.id (obj M N) := by
  apply Subtype.ext
  apply Module.Bimodule.RelativeTensor.hom_ext_right (R := R) (A := A)
  intro m n
  change (mapLeft (N := N) (Right.HomogeneousMap.id M)).1
      (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) =
    (Right.HomogeneousMap.id (obj M N)).1
      (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n)
  simp only [mapLeft_tmul, GradedModule.HomogeneousMap.id_apply]

/-- The identity on the second factor induces the identity graded relative tensor map. -/
@[simp]
theorem mapRight_id :
    mapRight (M := M) (Bimodule.Hom.id N) =
      Right.HomogeneousMap.id (obj M N) := by
  apply Subtype.ext
  apply Module.Bimodule.RelativeTensor.hom_ext_right (R := R) (A := A)
  intro m n
  change (mapRight (M := M) (Bimodule.Hom.id N)).1
      (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) =
    (Right.HomogeneousMap.id (obj M N)).1
      (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n)
  simp only [mapRight_tmul, Bimodule.id_apply, GradedModule.HomogeneousMap.id_apply]

/-- Maps induced in the first graded relative tensor factor preserve composition. -/
theorem mapLeft_comp (f : Right.HomogeneousMap M M' 0)
    (g : Right.HomogeneousMap M' M'' 0) :
    mapLeft (N := N) (Right.HomogeneousMap.compZero g f) =
      Right.HomogeneousMap.compZero (mapLeft (N := N) g) (mapLeft (N := N) f) := by
  apply Subtype.ext
  apply Module.Bimodule.RelativeTensor.hom_ext_right (R := R) (A := A)
  intro m n
  change (mapLeft (N := N) (Right.HomogeneousMap.compZero g f)).1
      (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) =
    (Right.HomogeneousMap.compZero (mapLeft (N := N) g) (mapLeft (N := N) f)).1
      (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n)
  simp only [Right.HomogeneousMap.compZero_apply, mapLeft_tmul]

/-- Maps induced in the second graded relative tensor factor preserve composition. -/
theorem mapRight_comp (f : Bimodule.Hom N N') (g : Bimodule.Hom N' N'') :
    mapRight (M := M) (Bimodule.Hom.comp g f) =
      Right.HomogeneousMap.compZero (mapRight (M := M) g) (mapRight (M := M) f) := by
  apply Subtype.ext
  apply Module.Bimodule.RelativeTensor.hom_ext_right (R := R) (A := A)
  intro m n
  change (mapRight (M := M) (Bimodule.Hom.comp g f)).1
      (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) =
    (Right.HomogeneousMap.compZero (mapRight (M := M) g) (mapRight (M := M) f)).1
      (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n)
  simp only [Right.HomogeneousMap.compZero_apply, mapRight_tmul,
    Bimodule.Hom.comp_toLinearMap, LinearMap.comp_apply]

/-- The maps induced in the two graded relative tensor factors commute. -/
theorem mapLeft_mapRight (f : Right.HomogeneousMap M M' 0) (g : Bimodule.Hom N N') :
    Right.HomogeneousMap.compZero (mapRight (M := M') g) (mapLeft (N := N) f) =
      Right.HomogeneousMap.compZero (mapLeft (N := N') f) (mapRight (M := M) g) := by
  apply Subtype.ext
  apply Module.Bimodule.RelativeTensor.hom_ext_right (R := R) (A := A)
  intro m n
  change (Right.HomogeneousMap.compZero (mapRight (M := M') g) (mapLeft (N := N) f)).1
      (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) =
    (Right.HomogeneousMap.compZero (mapLeft (N := N') f) (mapRight (M := M) g)).1
      (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n)
  simp only [Right.HomogeneousMap.compZero_apply, mapLeft_tmul, mapRight_tmul]

/-- The simultaneous graded relative tensor map can equivalently be formed in the opposite
factor order. -/
theorem map_eq_mapLeft_comp_mapRight
    (f : Right.HomogeneousMap M M' 0) (g : Bimodule.Hom N N') :
    map f g =
      Right.HomogeneousMap.compZero (mapLeft (N := N') f) (mapRight (M := M) g) := by
  exact mapLeft_mapRight f g

/-- Mapping both factors by identities is the identity graded relative tensor map. -/
@[simp]
theorem map_id :
    map (Right.HomogeneousMap.id M) (Bimodule.Hom.id N) =
      Right.HomogeneousMap.id (obj M N) := by
  simp only [map, mapLeft_id, mapRight_id, Right.HomogeneousMap.compZero_id]

/-- The simultaneous map with the identity in the first factor is `mapRight`. -/
@[simp]
theorem map_id_left (g : Bimodule.Hom N N') :
    map (Right.HomogeneousMap.id M) g = mapRight (M := M) g := by
  simp only [map, mapLeft_id, Right.HomogeneousMap.compZero_id]

/-- The simultaneous map with the identity in the second factor is `mapLeft`. -/
@[simp]
theorem map_id_right (f : Right.HomogeneousMap M M' 0) :
    map f (Bimodule.Hom.id N) = mapLeft (N := N) f := by
  simp only [map, mapRight_id, Right.HomogeneousMap.id_compZero]

/-- Simultaneous graded relative tensor maps preserve composition in both variables. -/
theorem map_comp (f : Right.HomogeneousMap M M' 0)
    (f' : Right.HomogeneousMap M' M'' 0) (g : Bimodule.Hom N N')
    (g' : Bimodule.Hom N' N'') :
    map (Right.HomogeneousMap.compZero f' f) (Bimodule.Hom.comp g' g) =
      Right.HomogeneousMap.compZero (map f' g') (map f g) := by
  apply Subtype.ext
  apply Module.Bimodule.RelativeTensor.hom_ext_right (R := R) (A := A)
  intro m n
  change (map (Right.HomogeneousMap.compZero f' f) (Bimodule.Hom.comp g' g)).1
      (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n) =
    (Right.HomogeneousMap.compZero (map f' g') (map f g)).1
      (Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) m n)
  simp only [Right.HomogeneousMap.compZero_apply, map_tmul,
    Bimodule.Hom.comp_toLinearMap, LinearMap.comp_apply]

private theorem mapLeft_add (f g : Right.HomogeneousMap M M' 0) :
    mapLeft (N := N) (f + g) = mapLeft (N := N) f + mapLeft (N := N) g := by
  apply Subtype.ext
  apply Module.Bimodule.RelativeTensor.hom_ext_right (R := R) (A := A)
  intro m n
  change (mapLeft (N := N) (f + g)).1 _ =
    (mapLeft (N := N) f).1 _ + (mapLeft (N := N) g).1 _
  rw [mapLeft_tmul, mapLeft_tmul, mapLeft_tmul]
  change Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) (f.1 m + g.1 m) n = _
  simp only [Module.Bimodule.RelativeTensor.tmul, TensorProduct.add_tmul, map_add]
  rfl

private theorem mapLeft_smul (r : R) (f : Right.HomogeneousMap M M' 0) :
    mapLeft (N := N) (r • f) = r • mapLeft (N := N) f := by
  apply Subtype.ext
  apply Module.Bimodule.RelativeTensor.hom_ext_right (R := R) (A := A)
  intro m n
  change (mapLeft (N := N) (r • f)).1 _ = r • (mapLeft (N := N) f).1 _
  rw [mapLeft_tmul, mapLeft_tmul]
  change Module.Bimodule.RelativeTensor.tmul (R := R) (A := A) (r • f.1 m) n = _
  simp only [Module.Bimodule.RelativeTensor.tmul, ← TensorProduct.smul_tmul', map_smul]
  rfl

-- The total graded Hom is a direct sum; composition on its degree-zero summands agrees
-- with composition of the underlying homogeneous maps.
private theorem degreeZeroHomEquiv_comp
    {K L P : Right.{i, x, v, u} 𝒜}
    (f : Right.HomogeneousMap K L 0) (g : Right.HomogeneousMap L P 0) :
    Right.degreeZeroHomEquiv K P (Right.HomogeneousMap.compZero g f) =
      Right.degreeZeroHomEquiv K L f ≫ Right.degreeZeroHomEquiv L P g := by
  apply WideSubcategory.hom_ext
  -- Give the auxiliary linear maps proved linearity fields before computing their values.
  -- This avoids copying the ambient total-Hom construction's unfinished proof fields.
  let component {m : ι} (q : Right.HomogeneousMap L P m) (n : ι) :
      Right.HomogeneousMap K L n →ₗ[R] Right.HomogeneousMap K P (n + m) :=
    { toFun p := Right.HomogeneousMap.comp q p
      map_add' := by
        intro p p'
        apply Subtype.ext
        apply LinearMap.ext
        intro x
        change (Right.HomogeneousMap.comp q (p + p')).1 x =
          (Right.HomogeneousMap.comp q p).1 x + (Right.HomogeneousMap.comp q p').1 x
        simp only [GradedModule.HomogeneousMap.comp_apply]
        exact map_add q.1 _ _
      map_smul' := by
        intro r p
        apply Subtype.ext
        apply LinearMap.ext
        intro x
        change (Right.HomogeneousMap.comp q (r • p)).1 x =
          r • (Right.HomogeneousMap.comp q p).1 x
        simp only [GradedModule.HomogeneousMap.comp_apply]
        exact q.1.map_smul_of_tower r _ }
  let postcomp {m : ι} (q : Right.HomogeneousMap L P m) :
      Right.Hom K L →ₗ[R] Right.Hom K P :=
    DirectSum.toModule R ι (Right.Hom K P) fun n ↦
      (Right.Hom.of K P (n + m)).comp (component q n)
  let postcompLinear (m : ι) :
      Right.HomogeneousMap L P m →ₗ[R] Right.Hom K L →ₗ[R] Right.Hom K P :=
    { toFun q := postcomp q
      map_add' := by
        intro q q'
        apply DirectSum.linearMap_ext
        intro n
        apply LinearMap.ext
        intro p
        change postcomp (q + q') (Right.Hom.of K L n p) =
          postcomp q (Right.Hom.of K L n p) + postcomp q' (Right.Hom.of K L n p)
        simp only [postcomp, Right.Hom.of, DirectSum.toModule_lof, LinearMap.comp_apply]
        rw [← (Right.Hom.of K P (n + m)).map_add]
        apply congrArg (Right.Hom.of K P (n + m))
        apply Subtype.ext
        apply LinearMap.ext
        intro x
        change (Right.HomogeneousMap.comp (q + q') p).1 x =
          (Right.HomogeneousMap.comp q p).1 x + (Right.HomogeneousMap.comp q' p).1 x
        simp only [GradedModule.HomogeneousMap.comp_apply]
        rfl
      map_smul' := by
        intro r q
        apply DirectSum.linearMap_ext
        intro n
        apply LinearMap.ext
        intro p
        change postcomp (r • q) (Right.Hom.of K L n p) =
          r • postcomp q (Right.Hom.of K L n p)
        simp only [postcomp, Right.Hom.of, DirectSum.toModule_lof, LinearMap.comp_apply]
        rw [← (Right.Hom.of K P (n + m)).map_smul]
        apply congrArg (Right.Hom.of K P (n + m))
        apply Subtype.ext
        apply LinearMap.ext
        intro x
        change (Right.HomogeneousMap.comp (r • q) p).1 x =
          r • (Right.HomogeneousMap.comp q p).1 x
        simp only [GradedModule.HomogeneousMap.comp_apply]
        rfl }
  change Right.Hom.of K P 0 (Right.HomogeneousMap.compZero g f) =
    (DirectSum.toModule R ι _ postcompLinear (Right.Hom.of L P 0 g))
      (Right.Hom.of K L 0 f)
  simp only [Right.Hom.of, DirectSum.toModule_lof, postcompLinear, postcomp, component,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
  have of_eq {a b : ι} (hab : a = b)
      (p : Right.HomogeneousMap K P a) (q : Right.HomogeneousMap K P b)
      (hpq : p.1 = q.1) : Right.Hom.of K P a p = Right.Hom.of K P b q := by
    subst b
    exact congrArg (Right.Hom.of K P a) (Subtype.ext hpq)
  apply of_eq (zero_add (0 : ι)).symm
  apply LinearMap.ext
  intro m
  simp only [Right.HomogeneousMap.compZero_apply, Right.HomogeneousMap.comp_apply]

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
  map_id := by
    intro M
    rw [show (Right.degreeZeroHomEquiv M.obj M.obj).symm (𝟙 M) =
        Right.HomogeneousMap.id M.obj from
      (Right.degreeZeroHomEquiv M.obj M.obj).symm_apply_eq.mpr rfl,
      RelativeTensor.mapLeft_id]
    rfl
  map_comp := by
    intro K L M f g
    obtain ⟨f, rfl⟩ := (Right.degreeZeroHomEquiv K.obj L.obj).surjective f
    obtain ⟨g, rfl⟩ := (Right.degreeZeroHomEquiv L.obj M.obj).surjective g
    rw [← degreeZeroHomEquiv_comp]
    simp only [LinearEquiv.symm_apply_apply]
    rw [RelativeTensor.mapLeft_comp, degreeZeroHomEquiv_comp]

/-- The fixed-bimodule tensor functor has the canonical graded relative tensor object at every
right graded module. -/
@[simp]
theorem functor_obj_obj (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι) :
    ((functor.{i, u, v, w, x, y} N).obj M).obj =
      RelativeTensor.obj M.obj N := rfl

/-- The fixed-bimodule tensor functor maps a degree-zero morphism by the canonical tensor map. -/
@[simp]
theorem functor_map (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝)
    {M M' : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι}
    (f : M ⟶ M') :
    (functor.{i, u, v, w, x, y} N).map f =
      Right.degreeZeroHomEquiv (RelativeTensor.obj M.obj N) (RelativeTensor.obj M'.obj N)
        (RelativeTensor.mapLeft (N := N)
          ((Right.degreeZeroHomEquiv M.obj M'.obj).symm f)) := rfl

/-- Tensoring with a fixed graded bimodule is additive on degree-zero morphisms. -/
instance functorAdditive (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    (functor.{i, u, v, w, x, y} N).Additive where
  map_add := by
    intro M M' f g
    simp only [functor_map, map_add, mapLeft_add]
    rfl

/-- Tensoring with a fixed graded bimodule is `R`-linear on degree-zero morphisms. -/
instance functorLinear (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    Functor.Linear R (functor.{i, u, v, w, x, y} N) where
  map_smul := by
    intro M M' f r
    simp only [functor_map, map_smul, mapLeft_smul]
    rfl

/-- A graded bimodule morphism induces a natural transformation between the corresponding
fixed-bimodule tensor functors. -/
@[stacks 09LN "naturality of graded relative tensor in the bimodule"]
def map (f : N ⟶ N') :
    functor.{i, u, v, w, x, y} N ⟶ functor.{i, u, v, w, x, y} N' where
  app M :=
    Right.degreeZeroHomEquiv (RelativeTensor.obj M.obj N) (RelativeTensor.obj M.obj N')
      (RelativeTensor.mapRight (M := M.obj) f)
  naturality := by
    intro M M' h
    obtain ⟨h, rfl⟩ := (Right.degreeZeroHomEquiv M.obj M'.obj).surjective h
    change Right.degreeZeroHomEquiv _ _
        (RelativeTensor.mapLeft (N := N)
          ((Right.degreeZeroHomEquiv M.obj M'.obj).symm
            (Right.degreeZeroHomEquiv M.obj M'.obj h))) ≫
        Right.degreeZeroHomEquiv _ _ (RelativeTensor.mapRight (M := M'.obj) f) =
      Right.degreeZeroHomEquiv _ _ (RelativeTensor.mapRight (M := M.obj) f) ≫
        Right.degreeZeroHomEquiv _ _
          (RelativeTensor.mapLeft (N := N')
            ((Right.degreeZeroHomEquiv M.obj M'.obj).symm
              (Right.degreeZeroHomEquiv M.obj M'.obj h)))
    simp only [LinearEquiv.symm_apply_apply, ← degreeZeroHomEquiv_comp]
    exact congrArg (Right.degreeZeroHomEquiv _ _) (RelativeTensor.mapLeft_mapRight h f)

/-- A component of the natural transformation induced by a graded bimodule morphism is the
canonical map on the second relative tensor factor. -/
@[simp]
theorem map_app (f : N ⟶ N')
    (M : CategoryTheory.GradedCategory.DegreeZero (R := R)
      (Right.{i, max i (max x y), v, u} 𝒜) ι) :
    (map.{i, u, v, w, x, y} f).app M =
      Right.degreeZeroHomEquiv (RelativeTensor.obj M.obj N) (RelativeTensor.obj M.obj N')
        (RelativeTensor.mapRight (M := M.obj) f) := rfl

/-- The identity graded bimodule morphism induces the identity tensor transformation. -/
@[simp]
theorem map_id (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    map.{i, u, v, w, x, y} (𝟙 N) = 𝟙 (functor.{i, u, v, w, x, y} N) := by
  apply NatTrans.ext
  funext M
  change Right.degreeZeroHomEquiv _ _ (RelativeTensor.mapRight (M := M.obj)
    (Bimodule.Hom.id N)) = 𝟙 _
  rw [RelativeTensor.mapRight_id]
  rfl

/-- Tensor transformations preserve composition of graded bimodule morphisms. -/
@[simp]
theorem map_comp (f : N ⟶ N') (g : N' ⟶ N'') :
    map.{i, u, v, w, x, y} (f ≫ g) =
      map.{i, u, v, w, x, y} f ≫ map.{i, u, v, w, x, y} g := by
  apply NatTrans.ext
  funext M
  change Right.degreeZeroHomEquiv _ _ (RelativeTensor.mapRight (M := M.obj)
      (Bimodule.Hom.comp g f)) =
    Right.degreeZeroHomEquiv _ _ (RelativeTensor.mapRight (M := M.obj) f) ≫
      Right.degreeZeroHomEquiv _ _ (RelativeTensor.mapRight (M := M.obj) g)
  rw [RelativeTensor.mapRight_comp, degreeZeroHomEquiv_comp]

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
  map_id := map_id
  map_comp := map_comp

/-- Evaluating the bimodule-parameter tensor functor gives the fixed-bimodule tensor functor.
-/
@[simp]
theorem bimoduleFunctor_obj (N : Bimodule.{i, y, w, v, u} 𝒜 𝒝) :
    (bimoduleFunctor.{i, u, v, w, x, y} (𝒜 := 𝒜) (𝒝 := 𝒝)).obj N =
      functor.{i, u, v, w, x, y} N := rfl

/-- The bimodule-parameter tensor functor maps a morphism to its canonical tensor natural
transformation. -/
@[simp]
theorem bimoduleFunctor_map {N N' : Bimodule.{i, y, w, v, u} 𝒜 𝒝} (f : N ⟶ N') :
    (bimoduleFunctor.{i, u, v, w, x, y} (𝒜 := 𝒜) (𝒝 := 𝒝)).map f =
      map.{i, u, v, w, x, y} f := rfl

end DegreeZero

end GradedModule.RelativeTensor
