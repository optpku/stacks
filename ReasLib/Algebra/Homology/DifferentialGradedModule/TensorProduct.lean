/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Complex
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Pairing
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.GradedPairing
import all ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Complex
import all ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Pairing

/-!
# Functoriality of relative tensor products of differential graded modules
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open CochainComplex.HomComplex
open ComplexShape
open HomologicalComplex

namespace DifferentialGradedModule.TensorProduct

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, x} R}

/-- Applying a degree-`j` homogeneous map in the right-module factor changes total degree
by `j`. -/
theorem mapDegree (p q n j : ℤ) (h : p + q = n) :
    (p + j) + q = n + j := by
  rw [← h]
  ac_rfl

/-- Apply a homogeneous map to the right-module factor of one pure tensor. -/
def rawMapPure (N : LeftDifferentialGradedModule.{u, w} A)
    {M M' : DifferentialGradedModule.{u, v} A} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom A M M' j)
    (n p q : ℤ) (h : p + q = n) (m : M.X p) (x : N.X q) :
    rawTerm M' N (n + j) :=
  (ιMapBifunctor (rightComplex M') (leftComplex N) (baseBifunctor (R := R))
    (up ℤ) (p + j) q (n + j) (mapDegree p q n j h)).hom (g p m ⊗ₜ[R] x)

/-- The map on one tensor summand induced by a homogeneous right-module map. -/
def rawMapComponent (N : LeftDifferentialGradedModule.{u, w} A)
    {M M' : DifferentialGradedModule.{u, v} A} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom A M M' j)
    (n p q : ℤ) (h : p + q = n) :
  baseTensor (R := R) (M.X p) (N.X q) ⟶ rawTerm M' N (n + j) :=
  ModuleCat.TensorProduct.lift R
    (LinearMap.mk₂ R (rawMapPure N g n p q h)
      (fun m m' x ↦ ((ιMapBifunctor (rightComplex M') (leftComplex N) (baseBifunctor (R := R))
          (up ℤ) (p + j) q (n + j) (mapDegree p q n j h)).hom.comp
          (((_root_.TensorProduct.mk R (M'.X (p + j)) (N.X q)).flip x).comp (g p))).map_add m m')
      (fun r m x ↦ ((ιMapBifunctor (rightComplex M') (leftComplex N) (baseBifunctor (R := R))
          (up ℤ) (p + j) q (n + j) (mapDegree p q n j h)).hom.comp
          (((_root_.TensorProduct.mk R (M'.X (p + j)) (N.X q)).flip x).comp (g p))).map_smul r m)
      (fun m x x' ↦ ((ιMapBifunctor (rightComplex M') (leftComplex N) (baseBifunctor (R := R))
          (up ℤ) (p + j) q (n + j) (mapDegree p q n j h)).hom.comp
          (_root_.TensorProduct.mk R (M'.X (p + j)) (N.X q) (g p m))).map_add x x')
      (fun r m x ↦ ((ιMapBifunctor (rightComplex M') (leftComplex N) (baseBifunctor (R := R))
          (up ℤ) (p + j) q (n + j) (mapDegree p q n j h)).hom.comp
          (_root_.TensorProduct.mk R (M'.X (p + j)) (N.X q) (g p m))).map_smul r x))

/-- The homogeneous map on unbalanced total tensor terms. -/
def rawMap (N : LeftDifferentialGradedModule.{u, w} A)
    {M M' : DifferentialGradedModule.{u, v} A} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom A M M' j) (n : ℤ) :
    rawTerm M N n →ₗ[R] rawTerm M' N (n + j) :=
  (mapBifunctorDesc (K₁ := rightComplex M) (K₂ := leftComplex N)
    (F := baseBifunctor (R := R)) (c := up ℤ)
    (fun p q h ↦ rawMapComponent N g n p q h)).hom

private theorem rawMap_ι_tmul (N : LeftDifferentialGradedModule.{u, w} A)
    {M M' : DifferentialGradedModule.{u, v} A} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom A M M' j)
    (n p q : ℤ) (h : p + q = n) (m : M.X p) (x : N.X q) :
    rawMap N g n
        ((ιMapBifunctor (rightComplex M) (leftComplex N) (baseBifunctor (R := R))
          (up ℤ) p q n h).hom (m ⊗ₜ[R] x)) = rawMapPure N g n p q h m x := by
  exact congrArg
    (fun f : baseTensor (R := R) (M.X p) (N.X q) ⟶ rawTerm M' N (n + j) ↦
      f (m ⊗ₜ[R] x))
    (ι_mapBifunctorDesc
      (K₁ := rightComplex M) (K₂ := leftComplex N) (F := baseBifunctor (R := R))
      (c := up ℤ) (fun a b h ↦ rawMapComponent N g n a b h) p q h)

/-- A homogeneous right-module map preserves the balancing relations. -/
theorem map_relations (N : LeftDifferentialGradedModule.{u, w} A)
    {M M' : DifferentialGradedModule.{u, v} A} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom A M M' j) (n : ℤ) :
    relations M N n ≤ Submodule.comap (rawMap N g n) (relations M' N (n + j)) := by
  apply Submodule.span_le.mpr
  rintro z ⟨p, i, q, h, m, a, x, rfl⟩
  change rawMap N g n (balanceGenerator M N p i q n h m a x) ∈ relations M' N (n + j)
  rw [balanceGenerator, map_sub, rawMap_ι_tmul, rawMap_ι_tmul]
  dsimp only [rawMapPure]
  rw [g.2 p i m a]
  erw [ι_tmul_cast_left M' N _ _ q (n + j)
    (DifferentialGradedModule.gradedHom_smul_index p i j)]
  exact Submodule.subset_span ⟨p + j, i, q, by omega, g p m, a, x, rfl⟩

/-- The homogeneous right-module map descended to the balancing quotients. -/
def mapLinear (N : LeftDifferentialGradedModule.{u, w} A)
    {M M' : DifferentialGradedModule.{u, v} A} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom A M M' j) (n : ℤ) :
    family M N n →ₗ[R] family M' N (n + j) :=
  (relations M N n).mapQ (relations M' N (n + j))
    (rawMap N g n) (map_relations N g n)

/-- A homogeneous map in the right factor acts on a pure tensor through its first entry. -/
@[simp]
theorem mapLinear_tmul (N : LeftDifferentialGradedModule.{u, w} A)
    {M M' : DifferentialGradedModule.{u, v} A} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom A M M' j)
    (p q : ℤ) (m : M.X p) (x : N.X q) :
    mapLinear N g (p + q) (tmul M N m x) =
      cast (congrArg (fun n : ℤ ↦ (family M' N n : Type (max v w)))
        (mapDegree p q (p + q) j rfl)) (tmul M' N (g p m) x) := by
  change mk M' N ((p + q) + j)
    (rawMap N g (p + q)
      ((ιMapBifunctor (rightComplex M) (leftComplex N) (baseBifunctor (R := R))
        (up ℤ) p q (p + q) rfl).hom (m ⊗ₜ[R] x))) = _
  rw [rawMap_ι_tmul]
  exact mk_ι_tmul M' N (p + j) q _ _ (g p m) x

/-- Regard an ordinary right-DG-module morphism as a homogeneous map of degree zero. -/
def gradedHomZero {M M' : DifferentialGradedModule.{u, v} A} (f : M ⟶ M') :
    DifferentialGradedModule.GradedHom A M M' 0 :=
  ⟨fun n ↦ ModuleCat.castLinearMap (congrArg M'.X (add_zero n).symm) (f.hom n), by
    intro p i m a
    dsimp only
    rw [castLinearMap_apply, castLinearMap_apply,
      apply_cast (fun p m ↦ M'.smul p i m a) (add_zero p).symm, cast_cast, f.comm_smul]⟩

/-- The degree-preserving quotient map induced by a right-DG-module morphism. -/
@[stacks 09LL "relative tensor map in the right module factor"]
def mapRightLinear (N : LeftDifferentialGradedModule.{u, w} A)
    {M M' : DifferentialGradedModule.{u, v} A} (f : M ⟶ M') (n : ℤ) :
    family M N n →ₗ[R] family M' N n :=
  ModuleCat.castLinearMap (congrArg (family M' N) (add_zero n))
    (mapLinear N (gradedHomZero f) n)

private theorem mapRightLinear_tmul (N : LeftDifferentialGradedModule.{u, w} A)
    {M M' : DifferentialGradedModule.{u, v} A} (f : M ⟶ M')
    (p q : ℤ) (m : M.X p) (x : N.X q) :
    mapRightLinear N f (p + q) (tmul M N m x) =
      tmul M' N (f.hom p m) x := by
  rw [mapRightLinear, castLinearMap_apply, mapLinear_tmul]
  change cast _ (cast _ (tmul M' N
    (ModuleCat.castLinearMap (congrArg M'.X (add_zero p).symm) (f.hom p) m) x)) = _
  rw [castLinearMap_apply, apply_cast (fun p m ↦ tmul M' N (p := p) m x) (add_zero p).symm,
    cast_cast, cast_cast]
  rfl


/-- The cochain map induced by a morphism of the right tensor factor. -/
@[stacks 09LL "relative tensor cochain map in the right factor"]
def mapRight (N : LeftDifferentialGradedModule.{u, w} A)
    {M M' : DifferentialGradedModule.{u, v} A} (f : M ⟶ M') :
    complex M N ⟶ complex M' N where
  f n := ModuleCat.ofHom (mapRightLinear N f n)
  comm' := by
    intro i j hij
    have hj : i + 1 = j := hij
    subst j
    apply family_hom_ext _ N
    intro p q hpq m x
    subst i
    change (complex _ N).d (p + q) ((p + q) + 1)
        (mapRightLinear N f (p + q) (tmul _ N m x)) =
      mapRightLinear N f ((p + q) + 1)
        ((complex _ N).d (p + q) ((p + q) + 1) (tmul _ N m x))
    rw [mapRightLinear_tmul, differential_tmul, differential_tmul, map_add, map_smul,
      apply_cast (fun n z ↦ mapRightLinear N f n z) (differentialLeftDegree p q),
      apply_cast (fun n z ↦ mapRightLinear N f n z) (differentialRightDegree p q),
      mapRightLinear_tmul, mapRightLinear_tmul, f.comm_d]

/-- A right-DG-module morphism acts on a pure tensor through its first entry. -/
@[simp]
theorem mapRight_tmul (N : LeftDifferentialGradedModule.{u, w} A)
    {M M' : DifferentialGradedModule.{u, v} A} (f : M ⟶ M')
    (p q : ℤ) (m : M.X p) (x : N.X q) :
    (mapRight N f).f (p + q) (tmul M N m x) =
      tmul M' N (f.hom p m) x := mapRightLinear_tmul N f p q m x

/-- The relative tensor complex as a functor of its right-module factor. -/
@[stacks 09LL "relative tensor functor in the right factor"]
def rightModuleFunctor (N : LeftDifferentialGradedModule.{u, w} A) :
    DifferentialGradedModule.{u, v} A ⥤
      CochainComplex (ModuleCat.{max v w} R) ℤ where
  obj M := complex M N
  map := mapRight N
  map_id := by
    intro M
    apply hom_ext M N
    intro p q m x
    rw [mapRight_tmul]
    rfl
  map_comp := by
    intro M M' M'' f g
    apply hom_ext M N
    intro p q m x
    change _ = (mapRight N g).f (p + q) ((mapRight N f).f (p + q) (tmul M N m x))
    rw [mapRight_tmul, mapRight_tmul, mapRight_tmul]
    rfl

/-- Apply a left-module morphism on one pure tensor summand. -/
def rawMapLeftPure (M : DifferentialGradedModule.{u, v} A)
    {N N' : LeftDifferentialGradedModule.{u, w} A} (g : N ⟶ N')
    (n p q : ℤ) (h : p + q = n) (m : M.X p) (x : N.X q) : rawTerm M N' n :=
  (ιMapBifunctor (rightComplex M) (leftComplex N') (baseBifunctor (R := R))
    (up ℤ) p q n h).hom (m ⊗ₜ[R] g.hom q x)

/-- The map on one tensor summand induced by a left-module morphism. -/
def rawMapLeftComponent (M : DifferentialGradedModule.{u, v} A)
    {N N' : LeftDifferentialGradedModule.{u, w} A} (g : N ⟶ N')
    (n p q : ℤ) (h : p + q = n) :
    baseTensor (R := R) (M.X p) (N.X q) ⟶ rawTerm M N' n :=
  ModuleCat.TensorProduct.lift R
    (LinearMap.mk₂ R (rawMapLeftPure M g n p q h)
      (fun m m' x ↦ ((ιMapBifunctor (rightComplex M) (leftComplex N') (baseBifunctor (R := R))
          (up ℤ) p q n h).hom.comp
          ((_root_.TensorProduct.mk R (M.X p) (N'.X q)).flip (g.hom q x))).map_add m m')
      (fun r m x ↦ ((ιMapBifunctor (rightComplex M) (leftComplex N') (baseBifunctor (R := R))
          (up ℤ) p q n h).hom.comp
          ((_root_.TensorProduct.mk R (M.X p) (N'.X q)).flip (g.hom q x))).map_smul r m)
      (fun m x x' ↦ ((ιMapBifunctor (rightComplex M) (leftComplex N') (baseBifunctor (R := R))
          (up ℤ) p q n h).hom.comp
          ((_root_.TensorProduct.mk R (M.X p) (N'.X q) m).comp (g.hom q))).map_add x x')
      (fun r m x ↦ ((ιMapBifunctor (rightComplex M) (leftComplex N') (baseBifunctor (R := R))
          (up ℤ) p q n h).hom.comp
          ((_root_.TensorProduct.mk R (M.X p) (N'.X q) m).comp (g.hom q))).map_smul r x))

/-- The map induced on unbalanced terms by a left-module morphism. -/
def rawMapLeft (M : DifferentialGradedModule.{u, v} A)
    {N N' : LeftDifferentialGradedModule.{u, w} A} (g : N ⟶ N') (n : ℤ) :
    rawTerm M N n →ₗ[R] rawTerm M N' n :=
  (mapBifunctorDesc (K₁ := rightComplex M) (K₂ := leftComplex N)
    (F := baseBifunctor (R := R)) (c := up ℤ)
    (fun p q h ↦ rawMapLeftComponent M g n p q h)).hom

private theorem rawMapLeft_ι_tmul (M : DifferentialGradedModule.{u, v} A)
    {N N' : LeftDifferentialGradedModule.{u, w} A} (g : N ⟶ N')
    (n p q : ℤ) (h : p + q = n) (m : M.X p) (x : N.X q) :
    rawMapLeft M g n
        ((ιMapBifunctor (rightComplex M) (leftComplex N) (baseBifunctor (R := R))
          (up ℤ) p q n h).hom (m ⊗ₜ[R] x)) = rawMapLeftPure M g n p q h m x := by
  exact congrArg
    (fun f : baseTensor (R := R) (M.X p) (N.X q) ⟶ rawTerm M N' n ↦ f (m ⊗ₜ[R] x))
    (ι_mapBifunctorDesc
      (K₁ := rightComplex M) (K₂ := leftComplex N) (F := baseBifunctor (R := R))
      (c := up ℤ) (fun a b h ↦ rawMapLeftComponent M g n a b h) p q h)

/-- A left-module morphism preserves the balancing relations. -/
theorem mapLeft_relations (M : DifferentialGradedModule.{u, v} A)
    {N N' : LeftDifferentialGradedModule.{u, w} A} (g : N ⟶ N') (n : ℤ) :
    relations M N n ≤ Submodule.comap (rawMapLeft M g n) (relations M N' n) := by
  apply Submodule.span_le.mpr
  rintro z ⟨p, i, q, h, m, a, x, rfl⟩
  change rawMapLeft M g n (balanceGenerator M N p i q n h m a x) ∈ relations M N' n
  rw [balanceGenerator, map_sub, rawMapLeft_ι_tmul, rawMapLeft_ι_tmul]
  dsimp only [rawMapLeftPure]
  rw [g.comm_smul]
  exact Submodule.subset_span ⟨p, i, q, h, m, a, g.hom q x, rfl⟩

/-- The quotient map induced by a left-module morphism. -/
@[stacks 09LL "relative tensor map in the left module factor"]
def mapLeftLinear (M : DifferentialGradedModule.{u, v} A)
    {N N' : LeftDifferentialGradedModule.{u, w} A} (g : N ⟶ N') (n : ℤ) :
    family M N n →ₗ[R] family M N' n :=
  (relations M N n).mapQ (relations M N' n)
    (rawMapLeft M g n) (mapLeft_relations M g n)

private theorem mapLeftLinear_tmul (M : DifferentialGradedModule.{u, v} A)
    {N N' : LeftDifferentialGradedModule.{u, w} A} (g : N ⟶ N')
    (p q : ℤ) (m : M.X p) (x : N.X q) :
    mapLeftLinear M g (p + q) (tmul M N m x) =
      tmul M N' m (g.hom q x) := by
  change mk M N' (p + q)
    (rawMapLeft M g (p + q)
      ((ιMapBifunctor (rightComplex M) (leftComplex N) (baseBifunctor (R := R))
        (up ℤ) p q (p + q) rfl).hom (m ⊗ₜ[R] x))) = _
  rw [rawMapLeft_ι_tmul]
  rfl


/-- The cochain map induced by a morphism of the left tensor factor. -/
@[stacks 09LL "relative tensor cochain map in the left factor"]
def mapLeft (M : DifferentialGradedModule.{u, v} A)
    {N N' : LeftDifferentialGradedModule.{u, w} A} (g : N ⟶ N') :
    complex M N ⟶ complex M N' where
  f n := ModuleCat.ofHom (mapLeftLinear M g n)
  comm' := by
    intro i j hij
    have hj : i + 1 = j := hij
    subst j
    apply family_hom_ext M _
    intro p q hpq m x
    subst i
    change (complex M _).d (p + q) ((p + q) + 1)
        (mapLeftLinear M g (p + q) (tmul M _ m x)) =
      mapLeftLinear M g ((p + q) + 1)
        ((complex M _).d (p + q) ((p + q) + 1) (tmul M _ m x))
    rw [mapLeftLinear_tmul, differential_tmul, differential_tmul, map_add, map_smul,
      apply_cast (fun n z ↦ mapLeftLinear M g n z) (differentialLeftDegree p q),
      apply_cast (fun n z ↦ mapLeftLinear M g n z) (differentialRightDegree p q),
      mapLeftLinear_tmul, mapLeftLinear_tmul, g.comm_d]

/-- A left-DG-module morphism acts on a pure tensor through its second entry. -/
@[simp]
theorem mapLeft_tmul (M : DifferentialGradedModule.{u, v} A)
    {N N' : LeftDifferentialGradedModule.{u, w} A} (g : N ⟶ N')
    (p q : ℤ) (m : M.X p) (x : N.X q) :
    (mapLeft M g).f (p + q) (tmul M N m x) =
      tmul M N' m (g.hom q x) := mapLeftLinear_tmul M g p q m x

/-- The relative tensor complex as a functor of its left-module factor. -/
@[stacks 09LL "relative tensor functor in the left factor"]
def leftModuleFunctor (M : DifferentialGradedModule.{u, v} A) :
    LeftDifferentialGradedModule.{u, w} A ⥤
      CochainComplex (ModuleCat.{max v w} R) ℤ where
  obj N := complex M N
  map := mapLeft M
  map_id := by
    intro N
    apply hom_ext M N
    intro p q m x
    rw [mapLeft_tmul]
    rfl
  map_comp := by
    intro N N' N'' f g
    apply hom_ext M N
    intro p q m x
    change _ = (mapLeft M g).f (p + q) ((mapLeft M f).f (p + q) (tmul M N m x))
    rw [mapLeft_tmul, mapLeft_tmul, mapLeft_tmul]
    rfl

/-- Section 22.12 (09LL): relative tensor product as a curried functor, first in the right
DG-module factor and then in the left DG-module factor. -/
@[stacks 09LL "relative tensor product functor of differential graded modules"]
def functor :
    DifferentialGradedModule.{u, v} A ⥤
      LeftDifferentialGradedModule.{u, w} A ⥤
        CochainComplex (ModuleCat.{max v w} R) ℤ where
  obj M := leftModuleFunctor M
  map f :=
    { app := fun N ↦ mapRight N f
      naturality := by
        intro N N' g
        apply hom_ext _ N
        intro p q m x
        change (mapRight N' f).f (p + q) ((mapLeft _ g).f (p + q) (tmul _ N m x)) =
          (mapLeft _ g).f (p + q) ((mapRight N f).f (p + q) (tmul _ N m x))
        rw [mapLeft_tmul, mapRight_tmul, mapRight_tmul, mapLeft_tmul] }
  map_id := by
    intro M
    apply NatTrans.ext
    funext N
    exact (rightModuleFunctor N).map_id M
  map_comp := by
    intro M M' M'' f g
    apply NatTrans.ext
    funext N
    exact (rightModuleFunctor N).map_comp f g

/-- The relative tensor complex, functorial simultaneously in its right and left DG-module
factors. -/
def uncurried :
    DifferentialGradedModule.{u, v} A × LeftDifferentialGradedModule.{u, w} A ⥤
      CochainComplex (ModuleCat.{max v w} R) ℤ :=
  CategoryTheory.Functor.uncurry.obj (functor (A := A))

/-- The uncurried tensor map applies the two factor maps to a homogeneous pure tensor. -/
@[stacks 09LL "uncurried relative tensor map on pure tensors"]
theorem uncurried_map_tmul
    {X Y : DifferentialGradedModule.{u, v} A × LeftDifferentialGradedModule.{u, w} A}
    (f : X ⟶ Y) (p q : ℤ) (m : X.1.X p) (x : X.2.X q) :
    (uncurried.map f).f (p + q) (tmul X.1 X.2 m x) =
      tmul Y.1 Y.2 (f.1.hom p m) (f.2.hom q x) := by
  change (mapLeft Y.1 f.2).f (p + q)
    ((mapRight X.2 f.1).f (p + q) (tmul X.1 X.2 m x)) = _
  rw [mapRight_tmul, mapLeft_tmul]

section UniverseInference

universe uR uA uM uN

variable {R' : Type uR} [CommRing R']
variable {A' : CochainDGAlgebra.{uR, uA} R'}

end UniverseInference

end DifferentialGradedModule.TensorProduct
