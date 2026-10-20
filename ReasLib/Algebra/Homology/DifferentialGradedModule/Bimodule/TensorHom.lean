/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct

/-!
# Tensor-Hom Adjunction for Differential Graded Bimodules

This file constructs homogeneous currying and uncurrying for the explicit relative tensor and
internal-Hom owners.  It packages the resulting degreewise linear equivalence as an isomorphism
of Hom complexes and as the adjunction on closed degree-zero categories.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory
open ComplexShape
open DifferentialGradedCategory
open HomologicalComplex
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule.TensorHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-- Reassociation of the target degree in homogeneous currying. -/
@[stacks 09LN "degree reassociation for homogeneous currying"]
theorem curryDegree (p q k : ℤ) :
    (p + q) + k = q + (p + k) := sorry

/-- Curry a homogeneous tensor map after fixing a homogeneous element of the first factor. -/
@[stacks 09LN "pointwise homogeneous currying"]
def curryValue (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} {k : ℤ}
    (f : DifferentialGradedModule.GradedHom B (Tensor.obj M N) P k)
    (p : ℤ) (m : M.X p) :
    DifferentialGradedModule.GradedHom B N.toRightModule P (p + k) :=
  ⟨fun q ↦ ModuleCat.castLinearMap
      (congrArg P.X ((add_assoc p q k).trans (add_left_comm p q k)))
      ((f (p + q)).comp (Tensor.tmulRight M N m)),
    sorry⟩

/-- Homogeneous currying in one fixed degree of the first factor. -/
@[stacks 09LN "degreewise homogeneous currying"]
def curryComponent (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} {k : ℤ}
    (f : DifferentialGradedModule.GradedHom B (Tensor.obj M N) P k) (p : ℤ) :
    M.X p →ₗ[R] (internalHom N P).X (p + k) where
  toFun := curryValue N f p
  map_add' := sorry
  map_smul' := sorry

/-- Curry a homogeneous map out of a relative tensor product. -/
@[stacks 09LT "homogeneous currying for the DG tensor-Hom correspondence"]
def curry (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} {k : ℤ}
    (f : DifferentialGradedModule.GradedHom B (Tensor.obj M N) P k) :
    DifferentialGradedModule.GradedHom A M (internalHom N P) k :=
  ⟨curryComponent N f, sorry⟩

/-- Evaluation of homogeneous currying on a pure tensor. -/
@[stacks 09LT "pure-tensor formula for DG tensor-Hom currying"]
theorem curry_apply (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} {k p q : ℤ}
    (f : DifferentialGradedModule.GradedHom B (Tensor.obj M N) P k)
    (m : M.X p) (x : N.X q) :
    asGradedHom N P (curry N f p m) q x =
      cast (congrArg (fun n : ℤ ↦ (P.X n : Type v)) (curryDegree p q k))
        (f (p + q) (Tensor.tmul M N m x)) := sorry

/-- Reassociation of the source and target degrees in homogeneous uncurrying. -/
@[stacks 09LN "degree reassociation for homogeneous uncurrying"]
theorem uncurryDegree (p q n k : ℤ) (h : p + q = n) :
    q + (p + k) = n + k := sorry

/-- Uncurrying on one homogeneous tensor summand. -/
@[stacks 09LN "pointwise homogeneous uncurrying"]
def uncurryComponent (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} {k : ℤ}
    (g : DifferentialGradedModule.GradedHom A M (internalHom N P) k)
    (n p q : ℤ) (h : p + q = n) :
    DifferentialGradedModule.TensorProduct.baseTensor (R := R) (M.X p) (N.X q) ⟶
      P.X (n + k) :=
  ModuleCat.TensorProduct.liftOfBilinear R
    (fun m x ↦ cast (congrArg (fun t : ℤ ↦ (P.X t : Type v))
      ((add_left_comm q p k).trans
        ((add_assoc p q k).symm.trans (congrArg (fun t : ℤ ↦ t + k) h))))
      (asGradedHom N P (g p m) q x)) sorry sorry sorry sorry

/-- The morphism out of the raw total tensor term defining homogeneous uncurrying. -/
@[stacks 09LN "raw homogeneous uncurrying morphism"]
def uncurryDesc (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} {k : ℤ}
    (g : DifferentialGradedModule.GradedHom A M (internalHom N P) k) (n : ℤ) :
    Tensor.rawTerm M N n ⟶ P.X (n + k) :=
  mapBifunctorDesc (K₁ := Tensor.leftComplex M) (K₂ := Tensor.rightComplex N)
    (F := DifferentialGradedModule.TensorProduct.baseBifunctor (R := R)) (c := up ℤ)
    (fun p q h ↦ uncurryComponent N g n p q h)

/-- The raw homogeneous uncurrying map before imposing the balancing quotient. -/
@[stacks 09LN "raw homogeneous uncurrying map"]
def uncurryRaw (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} {k : ℤ}
    (g : DifferentialGradedModule.GradedHom A M (internalHom N P) k) (n : ℤ) :
    Tensor.rawTerm M N n →ₗ[R] P.X (n + k) :=
  (uncurryDesc N g n).hom

/-- The raw uncurrying map kills every homogeneous balancing relation. -/
@[stacks 09LN "balancing relations for homogeneous uncurrying"]
theorem uncurry_relations (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} {k : ℤ}
    (g : DifferentialGradedModule.GradedHom A M (internalHom N P) k) (n : ℤ) :
    Tensor.relations M N n ≤ LinearMap.ker (uncurryRaw N g n) := sorry

/-- The uncurrying map descended to one degree of the relative tensor quotient. -/
@[stacks 09LN "quotient-level homogeneous uncurrying"]
def uncurryLinear (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} {k : ℤ}
    (g : DifferentialGradedModule.GradedHom A M (internalHom N P) k) (n : ℤ) :
    Tensor.family M N n →ₗ[R] P.X (n + k) :=
  (Tensor.relations M N n).liftQ (uncurryRaw N g n) (uncurry_relations N g n)

/-- Uncurry a homogeneous map into the fixed-source internal Hom. -/
@[stacks 09LT "homogeneous uncurrying for the DG tensor-Hom correspondence"]
def uncurry (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} {k : ℤ}
    (g : DifferentialGradedModule.GradedHom A M (internalHom N P) k) :
    DifferentialGradedModule.GradedHom B (Tensor.obj M N) P k :=
  ⟨uncurryLinear N g, sorry⟩

/-- Evaluation of homogeneous uncurrying on a pure tensor. -/
@[stacks 09LT "pure-tensor formula for DG tensor-Hom uncurrying"]
theorem uncurry_tmul (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} {k p q : ℤ}
    (g : DifferentialGradedModule.GradedHom A M (internalHom N P) k)
    (m : M.X p) (x : N.X q) :
    uncurry N g (p + q) (Tensor.tmul M N m x) =
      cast (congrArg (fun n : ℤ ↦ (P.X n : Type v)) (uncurryDegree p q (p + q) k rfl))
        (asGradedHom N P (g p m) q x) := sorry

/-- Degree-`k` tensor-Hom adjunction as an `R`-linear equivalence of homogeneous maps. -/
@[stacks 09LN "homogeneous DG tensor-Hom linear equivalence"]
def homEquiv (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    DifferentialGradedModule.GradedHom B (Tensor.obj M N) P k ≃ₗ[R]
      DifferentialGradedModule.GradedHom A M (internalHom N P) k where
  toFun := curry N
  invFun := uncurry N
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

/-- Currying through `homEquiv` evaluates on a pure tensor by homogeneous evaluation. -/
@[simp, stacks 09LN "pure-tensor formula for the DG tensor-Hom equivalence"]
theorem homEquiv_apply_tmul (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) {k p q : ℤ}
    (f : DifferentialGradedModule.GradedHom B (Tensor.obj M N) P k)
    (m : M.X p) (x : N.X q) :
    asGradedHom N P (homEquiv N M P k f p m) q x =
      cast (congrArg (fun n : ℤ ↦ (P.X n : Type v)) (curryDegree p q k))
        (f (p + q) (Tensor.tmul M N m x)) := sorry

/-- Uncurrying through the inverse of `homEquiv` evaluates on a pure tensor by homogeneous
evaluation. -/
@[simp, stacks 09LN "pure-tensor formula for the inverse DG tensor-Hom equivalence"]
theorem homEquiv_symm_tmul (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) {k p q : ℤ}
    (g : DifferentialGradedModule.GradedHom A M (internalHom N P) k)
    (m : M.X p) (x : N.X q) :
    (homEquiv N M P k).symm g (p + q) (Tensor.tmul M N m x) =
      cast (congrArg (fun n : ℤ ↦ (P.X n : Type v))
        (uncurryDegree p q (p + q) k rfl))
        (asGradedHom N P (g p m) q x) := sorry

/-- Degreewise tensor-Hom currying commutes with the differential on enriched Hom complexes. -/
@[simp, stacks 09LT "differential compatibility of DG tensor-Hom currying"]
theorem homEquiv_comm_d (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ)
    (f : DifferentialGradedModule.GradedHom B (Tensor.obj M N) P k) :
    homEquiv N M P (k + 1)
        (DifferentialGradedModule.gradedHomDifferential k f) =
      DifferentialGradedModule.gradedHomDifferential k
        (homEquiv N M P k f) := sorry

/-- Degreewise tensor-Hom uncurrying commutes with the differential on enriched Hom complexes. -/
@[simp, stacks 09LT "differential compatibility of DG tensor-Hom uncurrying"]
theorem homEquiv_symm_comm_d (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ)
    (g : DifferentialGradedModule.GradedHom A M (internalHom N P) k) :
    (homEquiv N M P (k + 1)).symm
        (DifferentialGradedModule.gradedHomDifferential k g) =
      DifferentialGradedModule.gradedHomDifferential k
        ((homEquiv N M P k).symm g) := sorry

/-- Currying in every degree gives a cochain map between the two Hom complexes. -/
@[stacks 09LT "forward cochain map of the DG tensor-Hom correspondence"]
def homComplexForward (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) :
    DifferentialGradedCategory.homComplex (Tensor.obj M N) P ⟶
      DifferentialGradedCategory.homComplex M (internalHom N P) where
  f k := ModuleCat.ofHom (homEquiv N M P k).toLinearMap
  comm' := sorry

/-- Uncurrying in every degree gives the inverse cochain map between Hom complexes. -/
@[stacks 09LT "inverse cochain map of the DG tensor-Hom correspondence"]
def homComplexBackward (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) :
    DifferentialGradedCategory.homComplex M (internalHom N P) ⟶
      DifferentialGradedCategory.homComplex (Tensor.obj M N) P where
  f k := ModuleCat.ofHom (homEquiv N M P k).symm.toLinearMap
  comm' := sorry

/-- Lemma 22.30.3 (09LN), DG clause: the tensor-Hom equivalence is an isomorphism of Hom
complexes. Naturality squares are provided by the sibling `TensorHom.Naturality` owner. -/
@[stacks 09LN "tensor-Hom isomorphism of DG Hom complexes"]
def homComplexIso (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) :
    DifferentialGradedCategory.homComplex (Tensor.obj M N) P ≅
      DifferentialGradedCategory.homComplex M (internalHom N P) where
  hom := homComplexForward N M P
  inv := homComplexBackward N M P
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward Hom-complex isomorphism has `homEquiv` as its degree-`k` component. -/
@[simp, stacks 09LT "degree component of the forward DG tensor-Hom map"]
theorem homComplexIso_hom_f (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (homComplexIso N M P).hom.f k =
      ModuleCat.ofHom (homEquiv N M P k).toLinearMap := sorry

/-- The inverse Hom-complex isomorphism has inverse `homEquiv` as its degree-`k` component. -/
@[simp, stacks 09LT "degree component of the inverse DG tensor-Hom map"]
theorem homComplexIso_inv_f (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : DifferentialGradedModule.{u, v} A)
    (P : DifferentialGradedModule.{u, v} B) (k : ℤ) :
    (homComplexIso N M P).inv.f k =
      ModuleCat.ofHom (homEquiv N M P k).symm.toLinearMap := sorry

/-- The tensor-Hom equivalence restricted to closed degree-zero morphisms, retaining its
`R`-linear structure. -/
@[stacks 09LN "closed DG tensor-Hom linear equivalence"]
def compHomLinearEquiv (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : Comp R (DifferentialGradedModule.{u, v} A))
    (P : Comp R (DifferentialGradedModule.{u, v} B)) :
    ((Tensor.dgFunctor N).mapComp.obj M ⟶ P) ≃ₗ[R]
      (M ⟶ (internalHomDgFunctor N).mapComp.obj P) where
  toFun f := ⟨homEquiv N M.obj P.obj 0 f.val, sorry⟩
  invFun g := ⟨(homEquiv N M.obj P.obj 0).symm g.val, sorry⟩
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

/-- The plain closed tensor-Hom equivalence used by categorical adjunctions. -/
@[stacks 09LN "closed DG tensor-Hom equivalence"]
def compHomEquiv (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : Comp R (DifferentialGradedModule.{u, v} A))
    (P : Comp R (DifferentialGradedModule.{u, v} B)) :
    ((Tensor.dgFunctor N).mapComp.obj M ⟶ P) ≃
      (M ⟶ (internalHomDgFunctor N).mapComp.obj P) :=
  (compHomLinearEquiv N M P).toEquiv

/-- Closed currying is the degree-zero restriction of `homEquiv`. -/
@[simp, stacks 09LN "degree-zero value of closed DG tensor-Hom currying"]
theorem compHomEquiv_val (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : Comp R (DifferentialGradedModule.{u, v} A))
    (P : Comp R (DifferentialGradedModule.{u, v} B))
    (f : (Tensor.dgFunctor N).mapComp.obj M ⟶ P) :
    (compHomEquiv N M P f).val = homEquiv N M.obj P.obj 0 f.val := sorry

/-- Closed uncurrying is the inverse degree-zero restriction of `homEquiv`. -/
@[simp, stacks 09LN "degree-zero value of closed DG tensor-Hom uncurrying"]
theorem compHomEquiv_symm_val (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : Comp R (DifferentialGradedModule.{u, v} A))
    (P : Comp R (DifferentialGradedModule.{u, v} B))
    (g : M ⟶ (internalHomDgFunctor N).mapComp.obj P) :
    ((compHomEquiv N M P).symm g).val =
      (homEquiv N M.obj P.obj 0).symm g.val := sorry

/-- The closed tensor-Hom core equivalence, with its naturality fields exposed for reuse. -/
@[stacks 09LN "core natural equivalence for closed DG tensor-Hom"]
def coreHomEquiv (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    Adjunction.CoreHomEquiv (Tensor.dgFunctor N).mapComp (internalHomDgFunctor N).mapComp where
  homEquiv := fun M P ↦ compHomEquiv (R := R) N M P
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

/-- Tensoring with `N` is left adjoint to fixed-source internal Hom on closed degree-zero
categories. -/
@[stacks 09LN "closed DG tensor-Hom adjunction"]
def adjunction (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (Tensor.dgFunctor N).mapComp ⊣ (internalHomDgFunctor N).mapComp :=
  Adjunction.mkOfHomEquiv (coreHomEquiv N)

namespace Closed

/-- The closed fixed-bimodule tensor functor is recognized as a left adjoint. -/
@[stacks 09LN "closed DG tensor functor is a left adjoint"]
instance tensorIsLeftAdjoint (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (Tensor.dgFunctor N).mapComp.IsLeftAdjoint := sorry

/-- The closed fixed-source internal-Hom functor is recognized as a right adjoint. -/
@[stacks 09LN "closed DG internal Hom functor is a right adjoint"]
instance internalHomIsRightAdjoint (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (internalHomDgFunctor N).mapComp.IsRightAdjoint := sorry

end Closed

/-- The Hom equivalence of the concrete tensor-Hom adjunction is closed currying. -/
@[stacks 09LN "Hom equivalence of the closed DG tensor-Hom adjunction"]
theorem adjunction_homEquiv (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : Comp R (DifferentialGradedModule.{u, v} A))
    (P : Comp R (DifferentialGradedModule.{u, v} B)) :
    (adjunction N).homEquiv M P = compHomEquiv N M P := sorry

/-- The adjunction unit is closed currying of the identity tensor morphism. -/
@[stacks 09LN "unit of the closed DG tensor-Hom adjunction"]
theorem adjunction_unit_app (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : Comp R (DifferentialGradedModule.{u, v} A)) :
    (adjunction N).unit.app M =
      compHomEquiv N M ((Tensor.dgFunctor N).mapComp.obj M)
        (𝟙 ((Tensor.dgFunctor N).mapComp.obj M)) := sorry

/-- The adjunction counit is closed uncurrying of the identity internal-Hom morphism. -/
@[stacks 09LN "counit of the closed DG tensor-Hom adjunction"]
theorem adjunction_counit_app (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (P : Comp R (DifferentialGradedModule.{u, v} B)) :
    (adjunction N).counit.app P =
      (compHomEquiv N ((internalHomDgFunctor N).mapComp.obj P) P).symm
        (𝟙 ((internalHomDgFunctor N).mapComp.obj P)) := sorry

/-- Closed currying preserves the homotopy relation on tensor morphisms. -/
@[stacks 09LT "homotopy compatibility of DG tensor-Hom currying"]
theorem homotopyForward_sound (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B}
    {f g : CompHom (Tensor.obj M N) P}
    (h : Homotopic (Tensor.obj M N) P f g) :
    Homotopic M (internalHom N P)
      (compHomEquiv N ⟨M⟩ ⟨P⟩ f) (compHomEquiv N ⟨M⟩ ⟨P⟩ g) := sorry

/-- Closed uncurrying preserves the homotopy relation on internal-Hom morphisms. -/
@[stacks 09LT "homotopy compatibility of DG tensor-Hom uncurrying"]
theorem homotopyBackward_sound (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B}
    {f g : CompHom M (internalHom N P)}
    (h : Homotopic M (internalHom N P) f g) :
    Homotopic (Tensor.obj M N) P
      ((compHomEquiv N ⟨M⟩ ⟨P⟩).symm f)
      ((compHomEquiv N ⟨M⟩ ⟨P⟩).symm g) := sorry

/-- Currying on homotopy classes, defined by mapping closed representatives. -/
@[stacks 09LT "currying on DG homotopy classes"]
def homotopyForward (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} :
    HomotopyClass (Tensor.obj M N) P → HomotopyClass M (internalHom N P) :=
  _root_.Quotient.map (compHomEquiv N ⟨M⟩ ⟨P⟩)
    (fun _ _ h ↦ homotopyForward_sound N h)

/-- Uncurrying on homotopy classes, defined by mapping closed representatives. -/
@[stacks 09LT "uncurrying on DG homotopy classes"]
def homotopyBackward (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B} :
    HomotopyClass M (internalHom N P) → HomotopyClass (Tensor.obj M N) P :=
  _root_.Quotient.map (compHomEquiv N ⟨M⟩ ⟨P⟩).symm
    (fun _ _ h ↦ homotopyBackward_sound N h)

/-- Tensor-Hom currying on DG homotopy-category morphisms, retaining its `R`-linear
structure. -/
@[stacks 09LT "linear tensor-Hom equivalence on DG homotopy categories"]
def homotopyHomLinearEquiv (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : K R (DifferentialGradedModule.{u, v} A))
    (P : K R (DifferentialGradedModule.{u, v} B)) :
    ((Tensor.dgFunctor N).mapK.obj M ⟶ P) ≃ₗ[R]
      (M ⟶ (internalHomDgFunctor N).mapK.obj P) where
  toFun := homotopyForward N
  invFun := homotopyBackward N
  map_add' := sorry
  map_smul' := sorry
  left_inv := sorry
  right_inv := sorry

/-- The plain homotopy-category tensor-Hom equivalence used by categorical adjunctions. -/
@[stacks 09LT "homotopy DG tensor-Hom equivalence"]
def homotopyHomEquiv (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : K R (DifferentialGradedModule.{u, v} A))
    (P : K R (DifferentialGradedModule.{u, v} B)) :
    ((Tensor.dgFunctor N).mapK.obj M ⟶ P) ≃
      (M ⟶ (internalHomDgFunctor N).mapK.obj P) :=
  (homotopyHomLinearEquiv N M P).toEquiv

/-- Homotopy currying computes on a represented closed morphism. -/
@[simp, stacks 09LT "represented-map formula for DG tensor-Hom currying"]
theorem homotopyHomLinearEquiv_toHomotopyClass
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B}
    (f : CompHom (Tensor.obj M N) P) :
    homotopyHomLinearEquiv N (⟨M⟩ : K R _) (⟨P⟩ : K R _) f.toHomotopyClass =
      (compHomLinearEquiv N (⟨M⟩ : Comp R _) (⟨P⟩ : Comp R _) f).toHomotopyClass := sorry

/-- Homotopy uncurrying computes on a represented closed morphism. -/
@[simp, stacks 09LT "represented-map formula for DG tensor-Hom uncurrying"]
theorem homotopyHomLinearEquiv_symm_toHomotopyClass
    (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    {M : DifferentialGradedModule.{u, v} A}
    {P : DifferentialGradedModule.{u, v} B}
    (g : CompHom M (internalHom N P)) :
    (homotopyHomLinearEquiv N (⟨M⟩ : K R _) (⟨P⟩ : K R _)).symm
        g.toHomotopyClass =
      ((compHomLinearEquiv N (⟨M⟩ : Comp R _) (⟨P⟩ : Comp R _)).symm
        g).toHomotopyClass := sorry

/-- The homotopy-category tensor-Hom core equivalence, separated from adjunction assembly. -/
@[stacks 09LT "core natural equivalence for DG homotopy tensor-Hom"]
def homotopyCoreHomEquiv (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    Adjunction.CoreHomEquiv (Tensor.dgFunctor N).mapK (internalHomDgFunctor N).mapK where
  homEquiv := fun M P ↦ homotopyHomEquiv (R := R) N M P
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

/-- Tensoring with `N` is left adjoint to fixed-source internal Hom on DG homotopy
categories. -/
@[stacks 09LT "tensor-Hom adjunction on DG homotopy categories"]
def homotopyAdjunction (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (Tensor.dgFunctor N).mapK ⊣ (internalHomDgFunctor N).mapK :=
  Adjunction.mkOfHomEquiv (homotopyCoreHomEquiv N)

namespace Homotopy

/-- The fixed-bimodule tensor functor on DG homotopy categories is recognized as a left
adjoint. -/
@[stacks 09LT "homotopy DG tensor functor is a left adjoint"]
instance tensorIsLeftAdjoint (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (Tensor.dgFunctor N).mapK.IsLeftAdjoint := sorry

/-- The fixed-source internal-Hom functor on DG homotopy categories is recognized as a right
adjoint. -/
@[stacks 09LT "homotopy DG internal Hom functor is a right adjoint"]
instance internalHomIsRightAdjoint (N : DifferentialGradedBimodule.{u, v, w, x} A B) :
    (internalHomDgFunctor N).mapK.IsRightAdjoint := sorry

end Homotopy

/-- The Hom equivalence of the homotopy-category tensor-Hom adjunction is quotient-level
currying. -/
@[stacks 09LT "Hom equivalence of the homotopy DG tensor-Hom adjunction"]
theorem homotopyAdjunction_homEquiv (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : K R (DifferentialGradedModule.{u, v} A))
    (P : K R (DifferentialGradedModule.{u, v} B)) :
    (homotopyAdjunction N).homEquiv M P = homotopyHomEquiv N M P := sorry

/-- The homotopy tensor-Hom adjunction unit is quotient-level currying of the identity. -/
@[stacks 09LT "unit of the homotopy DG tensor-Hom adjunction"]
theorem homotopyAdjunction_unit_app (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (M : K R (DifferentialGradedModule.{u, v} A)) :
    (homotopyAdjunction N).unit.app M =
      homotopyHomEquiv N M ((Tensor.dgFunctor N).mapK.obj M)
        (𝟙 ((Tensor.dgFunctor N).mapK.obj M)) := sorry

/-- The homotopy tensor-Hom adjunction counit is quotient-level uncurrying of the identity. -/
@[stacks 09LT "counit of the homotopy DG tensor-Hom adjunction"]
theorem homotopyAdjunction_counit_app (N : DifferentialGradedBimodule.{u, v, w, x} A B)
    (P : K R (DifferentialGradedModule.{u, v} B)) :
    (homotopyAdjunction N).counit.app P =
      (homotopyHomEquiv N ((internalHomDgFunctor N).mapK.obj P) P).symm
        (𝟙 ((internalHomDgFunctor N).mapK.obj P)) := sorry

section AdjointInstances

variable (N : DifferentialGradedBimodule.{u, v, w, x} A B)

#synth (Tensor.dgFunctor N).mapComp.IsLeftAdjoint
#synth (internalHomDgFunctor N).mapComp.IsRightAdjoint
#synth (Tensor.dgFunctor N).mapK.IsLeftAdjoint
#synth (internalHomDgFunctor N).mapK.IsRightAdjoint

end AdjointInstances

end DifferentialGradedBimodule.TensorHom
