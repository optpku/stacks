/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.Algebra.Category.CommAlgCat.Module
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic
public import ReasLib.RingTheory.AdicCompletion.InverseSystem
public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.AdicSystem

/-!
# Inverse limits of finite-type adic algebra systems

The inverse-limit functor sending a finite-type adic inverse system
`(B n)` to `lim B n`, together with explicit unit and counit comparison maps
against `toAdicSystem`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PNatInverseSystem
noncomputable section

universe u

namespace AdicAlgebraSystem

variable {A : Type u} [CommRing A]

/-- The `A`-algebra structure on an arbitrary stage of an inverse system over
`quotientSystem I`, obtained from `instAlgebra` at `OrderDual.ofDual i`. -/
instance instAlgebraObj (I : Ideal A) (B : Under (quotientSystem I))
    (i : OrderDual ℕ+) :
    Algebra A (B.right.obj i) :=
  instAlgebra I B (OrderDual.ofDual i)

/-- Transitions of an adic system commute with the coefficient algebra maps. -/
private theorem transitionAlgHom_laws (I : Ideal A) (B : Under (quotientSystem I)) {i j : OrderDual ℕ+} (f : i ⟶ j) :
    ∀ a : A, (B.right.map f).hom (algebraMap A (B.right.obj i) a) =
      algebraMap A (B.right.obj j) a := by
  sorry

/-- The transition `B i ⟶ B j` of an inverse system over `quotientSystem I`,
as an `A`-algebra map. -/
def transitionAlgHom (I : Ideal A) (B : Under (quotientSystem I))
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    B.right.obj i →ₐ[A] B.right.obj j where
  toRingHom := (B.right.map f).hom
  commutes' := by exact transitionAlgHom_laws I B f

/-- Unfolding of `transitionAlgHom` as the underlying ring homomorphism of the
inverse-system transition. -/
theorem transitionAlgHom_toRingHom (I : Ideal A) (B : Under (quotientSystem I))
    {i j : OrderDual ℕ+} (f : i ⟶ j) :
    (transitionAlgHom I B f).toRingHom = (B.right.map f).hom := by
  rfl

/-- Algebra transition maps preserve identity indices and composition. -/
private theorem stageDiagram_laws (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (∀ i : OrderDual ℕ+, CommAlgCat.ofHom (transitionAlgHom I B.obj (𝟙 i)) =
      𝟙 (CommAlgCat.of A (B.obj.right.obj i))) ∧
    (∀ {i j k : OrderDual ℕ+} (f : i ⟶ j) (g : j ⟶ k),
      CommAlgCat.ofHom (transitionAlgHom I B.obj (f ≫ g)) =
        CommAlgCat.ofHom (transitionAlgHom I B.obj f) ≫
          CommAlgCat.ofHom (transitionAlgHom I B.obj g)) := by
  sorry

/-- The diagram `n ↦ B n` of a finite-type adic system, valued in commutative
`A`-algebras. -/
def stageDiagram (I : Ideal A) (B : AdicAlgebraSystem A I) :
    PNatInverseSystem (CommAlgCat.{u} A) where
  obj i := CommAlgCat.of A (B.obj.right.obj i)
  map f := CommAlgCat.ofHom (transitionAlgHom I B.obj f)
  map_id := by exact (stageDiagram_laws I B).1
  map_comp := by exact (stageDiagram_laws I B).2

/-- Stages of `stageDiagram I B` are the stages of `B` as `A`-algebras. -/
theorem stageDiagram_obj (I : Ideal A) (B : AdicAlgebraSystem A I)
    (i : OrderDual ℕ+) :
    (stageDiagram I B).obj i = CommAlgCat.of A (B.obj.right.obj i) := by
  rfl

/-- Stage maps of a morphism are algebra maps and form a natural transformation. -/
private theorem stageDiagramMap_laws (I : Ideal A) {B B' : AdicAlgebraSystem A I} (f : B ⟶ B') :
    (∀ (i : OrderDual ℕ+) (a : A), ((Under.Hom.right f.hom).app i).hom
      (algebraMap A (B.obj.right.obj i) a) = algebraMap A (B'.obj.right.obj i) a) ∧
    (∀ h : ∀ (i : OrderDual ℕ+) (a : A), ((Under.Hom.right f.hom).app i).hom
      (algebraMap A (B.obj.right.obj i) a) = algebraMap A (B'.obj.right.obj i) a,
      let app := (fun i ↦ CommAlgCat.ofHom
        { toRingHom := ((Under.Hom.right f.hom).app i).hom
          commutes' := h i })
      ∀ {i j : OrderDual ℕ+} (g : i ⟶ j),
        (stageDiagram I B).map g ≫ app j = app i ≫ (stageDiagram I B').map g) := by
  sorry

/-- A morphism of finite-type adic systems induces a morphism of `A`-algebra diagrams. -/
def stageDiagramMap (I : Ideal A) {B B' : AdicAlgebraSystem A I} (f : B ⟶ B') :
    stageDiagram I B ⟶ stageDiagram I B' where
  app i :=
    CommAlgCat.ofHom
      { toRingHom := (Under.Hom.right f.hom).app i |>.hom
        commutes' := by exact (stageDiagramMap_laws I f).1 i }
  naturality := by
    intro first second transition
    exact (stageDiagramMap_laws I f).2 (stageDiagramMap_laws I f).1 transition

/-- The underlying `A`-module diagram of a finite-type adic system. -/
def stageModuleDiagram (I : Ideal A) (B : AdicAlgebraSystem A I) :
    PNatInverseSystem (ModuleCat.{u} A) :=
  stageDiagram I B ⋙ CommAlgCat.forgetToModule A

/-- Stages of `stageModuleDiagram` are the stages of `B` as `A`-modules. -/
theorem stageModuleDiagram_obj (I : Ideal A) (B : AdicAlgebraSystem A I)
    (i : OrderDual ℕ+) :
    (stageModuleDiagram I B).obj i =
      (CommAlgCat.forgetToModule A).obj ((stageDiagram I B).obj i) := by
  rfl

/-- The underlying commutative-ring diagram of a finite-type adic system. -/
def stageRingDiagram (I : Ideal A) (B : AdicAlgebraSystem A I) :
    PNatInverseSystem CommRingCat.{u} :=
  stageDiagram I B ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat.{u}

/-- Stages of `stageRingDiagram` are the underlying rings of the stages of
`B`. -/
theorem stageRingDiagram_obj (I : Ideal A) (B : AdicAlgebraSystem A I)
    (i : OrderDual ℕ+) :
    (stageRingDiagram I B).obj i =
      (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).obj
        ((stageDiagram I B).obj i) := by
  rfl


/-- The inverse limit `lim B n` of a finite-type adic system, as a commutative
`A`-algebra. -/
def limitObj (I : Ideal A) (B : AdicAlgebraSystem A I) : CommAlgCat.{u} A :=
  limit (stageDiagram I B)

/-- `limitObj` is the categorical limit of `stageDiagram`. -/
theorem limitObj_eq (I : Ideal A) (B : AdicAlgebraSystem A I) :
    limitObj I B = limit (stageDiagram I B) := by
  rfl

/-- For finitely generated `I`, the inverse limit of a finite-type adic system is
topologically of finite type. -/
instance instTopologicallyFiniteTypeLimitObj (I : Ideal A) [hI : Fact I.FG]
    (B : AdicAlgebraSystem A I) :
    Algebra.TopologicallyFiniteType I (limitObj I B) :=
  sorry

/-- Induced limit maps preserve identities and composition. -/
private theorem limitFunctor_laws (I : Ideal A) (hI : I.FG) :
    (∀ B : AdicAlgebraSystem A I,
      limMap (stageDiagramMap I (𝟙 B)) = 𝟙 (limitObj I B)) ∧
    (∀ {B C D : AdicAlgebraSystem A I} (f : B ⟶ C) (g : C ⟶ D),
      limMap (stageDiagramMap I (f ≫ g)) =
        limMap (stageDiagramMap I f) ≫ limMap (stageDiagramMap I g)) := by
  sorry

/-- The inverse-limit functor from finite-type adic systems to topologically finite type algebras sending `(B n)` to `lim B n`. -/
def limitFunctor (I : Ideal A) (hI : I.FG) :
    AdicAlgebraSystem A I ⥤ CommAlgCat.TopologicallyFiniteType.{u} A I where
  obj B := ⟨limitObj I B, instTopologicallyFiniteTypeLimitObj I (hI := ⟨hI⟩) B⟩
  map f := ObjectProperty.homMk (limMap (stageDiagramMap I f))
  map_id B := by exact congrArg ObjectProperty.homMk ((limitFunctor_laws I hI).1 B)
  map_comp f g := by exact congrArg ObjectProperty.homMk ((limitFunctor_laws I hI).2 f g)

/-- On objects, `limitFunctor` is `limitObj`. -/
theorem limitFunctor_obj (I : Ideal A) (hI : I.FG) (B : AdicAlgebraSystem A I) :
    ((limitFunctor I hI).obj B).obj = limitObj I B := by
  rfl

/-- On morphisms, `limitFunctor` is induced by `limMap` of `stageDiagramMap`. -/
theorem limitFunctor_map (I : Ideal A) (hI : I.FG)
    {B B' : AdicAlgebraSystem A I} (f : B ⟶ B') :
    ((limitFunctor I hI).map f).hom = limMap (stageDiagramMap I f) := by
  rfl

/-- The canonical `A`-algebra map from a complete algebra to a finite adic
quotient stage of its quotient system. -/
def completeQuotientAlgHom (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    (n : ℕ+) :
    B →ₐ[A] (CommAlgCat.adicQuotientUnder I B).right.stage n where
  toRingHom := (Ideal.Quotient.mkₐ A ((I ^ (n : ℕ)).map (algebraMap A B))).toRingHom
  commutes' := by
    intro coefficient
    rfl

/-- The quotient maps of a complete algebra form a cone over its adic system. -/
private theorem completeQuotientCone_naturality (I : Ideal A) (B : CommAlgCat.TopologicallyFiniteType.{u} A I) :
    ∀ {i j : OrderDual ℕ+} (f : i ⟶ j),
      ((Functor.const (OrderDual ℕ+)).obj (B.obj)).map f ≫
        CommAlgCat.ofHom (completeQuotientAlgHom I B.obj (OrderDual.ofDual j)) = CommAlgCat.ofHom (completeQuotientAlgHom I B.obj (OrderDual.ofDual i)) ≫ (stageDiagram I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)).map f := by
  sorry

/-- The cone of quotient maps `B ⟶ B ⧸ I ^ n B` on the image under
`toAdicSystem`. -/
def completeQuotientCone (I : Ideal A)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) :
    Cone (stageDiagram I
      ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) where
  pt := B.obj
  π :=
    { app := fun i ↦
        CommAlgCat.ofHom (completeQuotientAlgHom I B.obj (OrderDual.ofDual i))
      naturality := by
        intro first second transition
        exact completeQuotientCone_naturality I B transition }

/-- The canonical comparison `B ⟶ lim (B ⧸ I ^ n B)` from the quotient cone. -/
def toLimitObjAlgHom (I : Ideal A)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) :
    B.obj →ₐ[A]
      limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B) :=
  (limit.lift
      (stageDiagram I
        ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B))
      (completeQuotientCone I B)).hom

/-- Completeness along `I` implies completeness along the extended ideal
`I B`. -/
instance instIsAdicComplete_map (I : Ideal A) (B : Type u) [CommRing B]
    [Algebra A B] [IsAdicComplete I B] :
    IsAdicComplete (I.map (algebraMap A B)) B :=
  (IsAdicComplete.map_algebraMap_iff I B).mpr inferInstance

/-- Limit projections onto adic quotient stages preserve the algebra operations. -/
private theorem limitObj_π_quotient_laws (I : Ideal A) (B : CommAlgCat.TopologicallyFiniteType.{u} A I) (n : ℕ+) :
    (((limit.π (stageDiagram I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) (OrderDual.toDual n)).hom) (1 : (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B))) = (1 : (B.obj ⧸ (I ^ (n : ℕ)).map (algebraMap A B.obj)))) ∧
    (∀ x y, ((limit.π (stageDiagram I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) (OrderDual.toDual n)).hom) (x * y) = ((limit.π (stageDiagram I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) (OrderDual.toDual n)).hom) x * ((limit.π (stageDiagram I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) (OrderDual.toDual n)).hom) y) ∧
    (((limit.π (stageDiagram I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) (OrderDual.toDual n)).hom) 0 = 0) ∧
    (∀ x y, ((limit.π (stageDiagram I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) (OrderDual.toDual n)).hom) (x + y) = ((limit.π (stageDiagram I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) (OrderDual.toDual n)).hom) x + ((limit.π (stageDiagram I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) (OrderDual.toDual n)).hom) y) ∧
    (∀ a : A, ((limit.π (stageDiagram I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) (OrderDual.toDual n)).hom) (algebraMap A (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) a) = algebraMap A (B.obj ⧸ (I ^ (n : ℕ)).map (algebraMap A B.obj)) a) := by
  sorry

/-- Projection of `lim (B ⧸ I ^ n B)` onto a positive adic quotient of `B`. -/
def limitObj_π_quotient (I : Ideal A)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) (n : ℕ+) :
    limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B) →ₐ[A]
      B.obj ⧸ (I ^ (n : ℕ)).map (algebraMap A B.obj) where
  toFun :=
    (limit.π
        (stageDiagram I
          ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B))
        (OrderDual.toDual n)).hom
  map_one' := by exact (limitObj_π_quotient_laws I B n).1
  map_mul' := by exact (limitObj_π_quotient_laws I B n).2.1
  map_zero' := by exact (limitObj_π_quotient_laws I B n).2.2.1
  map_add' := by exact (limitObj_π_quotient_laws I B n).2.2.2.1
  commutes' := by exact (limitObj_π_quotient_laws I B n).2.2.2.2

/-- The constant zero map into a zeroth adic quotient is an algebra map. -/
private theorem limitObjEvalFamily_zero_laws (I : Ideal A) (B : CommAlgCat.TopologicallyFiniteType.{u} A I) (n : ℕ) (hn : ¬ 0 < n) :
    ((fun _ : (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) ↦ (0 : (B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n))) (1 : (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B))) = (1 : (B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n))) ∧
    (∀ x y, (fun _ : (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) ↦ (0 : (B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n))) (x * y) = (fun _ : (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) ↦ (0 : (B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n))) x * (fun _ : (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) ↦ (0 : (B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n))) y) ∧
    ((fun _ : (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) ↦ (0 : (B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n))) 0 = 0) ∧
    (∀ x y, (fun _ : (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) ↦ (0 : (B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n))) (x + y) = (fun _ : (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) ↦ (0 : (B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n))) x + (fun _ : (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) ↦ (0 : (B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n))) y) ∧
    (∀ a : A, (fun _ : (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) ↦ (0 : (B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n))) (algebraMap A (limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B)) a) = algebraMap A (B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n) a) := by
  sorry

/-- Evaluation of the inverse limit of `(B ⧸ I ^ n B)` at a nonnegative stage,
as a map into `B ⧸ (I B) ^ n`. -/
def limitObjEvalFamily (I : Ideal A)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) (n : ℕ) :
    limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B) →ₐ[A]
      B.obj ⧸ (I.map (algebraMap A B.obj)) ^ n :=
  if hn : 0 < n then
    (Ideal.quotientEquivAlgOfEq A
        (Ideal.map_pow (algebraMap A B.obj) I n)).toAlgHom.comp
      (limitObj_π_quotient I B ⟨n, hn⟩)
  else
    { toFun := fun _ ↦ 0
      map_one' := by exact (limitObjEvalFamily_zero_laws I B n hn).1
      map_mul' := by exact (limitObjEvalFamily_zero_laws I B n hn).2.1
      map_zero' := by exact (limitObjEvalFamily_zero_laws I B n hn).2.2.1
      map_add' := by exact (limitObjEvalFamily_zero_laws I B n hn).2.2.2.1
      commutes' := by exact (limitObjEvalFamily_zero_laws I B n hn).2.2.2.2 }

/-- Compatibility of `limitObjEvalFamily` with the adic quotient tower. -/
theorem limitObjEvalFamily_comp (I : Ideal A)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp
        (limitObjEvalFamily I B n) =
      limitObjEvalFamily I B m :=
  sorry

/-- The inverse comparison `lim (B ⧸ I ^ n B) ⟶ B` for a topologically finite type algebra, via
`AdicCompletion.liftAlgHom` and `AdicCompletion.ofAlgEquiv`. -/
def fromLimitObjAlgHom (I : Ideal A)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) :
    limitObj I ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B) →ₐ[A]
      B.obj :=
  ((AdicCompletion.ofAlgEquiv (I.map (algebraMap A B.obj))).symm.toAlgHom.restrictScalars
        A).comp
    (AdicCompletion.liftAlgHom (I.map (algebraMap A B.obj))
      (limitObjEvalFamily I B) (limitObjEvalFamily_comp I B))

/-- The canonical maps between a complete algebra and its quotient-system limit are inverse. -/
private theorem completeLimitAlgEquiv_laws (I : Ideal A) (hI : I.FG) (B : CommAlgCat.TopologicallyFiniteType.{u} A I) :
    (toLimitObjAlgHom I B).comp (fromLimitObjAlgHom I B) = AlgHom.id A _ ∧
    (fromLimitObjAlgHom I B).comp (toLimitObjAlgHom I B) = AlgHom.id A _ := by
  sorry

/-- The canonical algebra equivalence `B ≃ₐ[A] lim (B ⧸ I ^ n B)` for an
I-adically complete A-algebra with finite-type special fiber. -/
def completeLimitAlgEquiv (I : Ideal A) (hI : I.FG)
    (B : CommAlgCat.TopologicallyFiniteType.{u} A I) :
    B.obj ≃ₐ[A]
      ((CommAlgCat.TopologicallyFiniteType.toAdicSystem I ⋙
          limitFunctor I hI).obj B).obj :=
  AlgEquiv.ofAlgHom (toLimitObjAlgHom I B) (fromLimitObjAlgHom I B) (by exact (completeLimitAlgEquiv_laws I hI B).1)
    (by exact (completeLimitAlgEquiv_laws I hI B).2)

/-- Coefficient maps commute with ring-stage transitions. -/
private theorem algebraMapRingCone_naturality (I : Ideal A) (B : AdicAlgebraSystem A I) :
    ∀ {i j : OrderDual ℕ+} (f : i ⟶ j),
      ((Functor.const (OrderDual ℕ+)).obj (CommRingCat.of A)).map f ≫
        CommRingCat.ofHom (algebraMap A ((stageDiagram I B).obj j)) = CommRingCat.ofHom (algebraMap A ((stageDiagram I B).obj i)) ≫ (stageRingDiagram I B).map f := by
  sorry

/-- The constant ring cone on `stageRingDiagram` with vertex `A`. -/
def algebraMapRingCone (I : Ideal A) (B : AdicAlgebraSystem A I) :
    Cone (stageRingDiagram I B) where
  pt := CommRingCat.of A
  π.app i :=
    CommRingCat.ofHom (algebraMap A ((stageDiagram I B).obj i))
  π.naturality := by
        intro first second transition
        exact algebraMapRingCone_naturality I B transition

/-- The vertex of `algebraMapRingCone` is `A`. -/
theorem algebraMapRingCone_pt (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (algebraMapRingCone I B).pt = CommRingCat.of A := by
  rfl

/-- The coefficient-limit map is central and its multiplication gives scalar action. -/
private theorem limitRingAlgebra_laws (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (∀ a : A, ∀ x : (limit (stageRingDiagram I B) : CommRingCat.{u}),
      ((limit.lift (stageRingDiagram I B) (algebraMapRingCone I B)).hom) a * x = x * ((limit.lift (stageRingDiagram I B) (algebraMapRingCone I B)).hom) a) ∧
    (∀ a : A, ∀ x : (limit (stageRingDiagram I B) : CommRingCat.{u}),
      ((limit.lift (stageRingDiagram I B) (algebraMapRingCone I B)).hom) a * x = ((limit.lift (stageRingDiagram I B) (algebraMapRingCone I B)).hom) a * x) := by
  sorry

/-- The inverse limit of the underlying ring diagram carries its canonical
`A`-algebra structure, with structure map the limit of the stage structure
maps. -/
instance instAlgebra_limit_stageRingDiagram (I : Ideal A)
    (B : AdicAlgebraSystem A I) :
    Algebra A (limit (stageRingDiagram I B) : CommRingCat.{u}) where
  smul r x :=
    (limit.lift (stageRingDiagram I B) (algebraMapRingCone I B)).hom r * x
  algebraMap :=
    (limit.lift (stageRingDiagram I B) (algebraMapRingCone I B)).hom
  commutes' := by exact (limitRingAlgebra_laws I B).1
  smul_def' := by exact (limitRingAlgebra_laws I B).2

/-- The structure map of the ring-limit algebra is the lift of
`algebraMapRingCone`. -/
theorem algebraMap_limit_stageRingDiagram (I : Ideal A)
    (B : AdicAlgebraSystem A I) :
    algebraMap A (limit (stageRingDiagram I B) : CommRingCat.{u}) =
      (limit.lift (stageRingDiagram I B) (algebraMapRingCone I B)).hom := by
  rfl

/-- The forgotten algebra-limit projections form a compatible cone. -/
private theorem limitObjRingCone_naturality (I : Ideal A) (B : AdicAlgebraSystem A I) :
    ∀ {i j : OrderDual ℕ+} (f : i ⟶ j),
      ((Functor.const (OrderDual ℕ+)).obj ((forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).obj (limitObj I B))).map f ≫
        (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).map (limit.π (stageDiagram I B) j) =
      (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).map (limit.π (stageDiagram I B) i) ≫
        (stageRingDiagram I B).map f := by
  sorry

/-- The forgotten limit cone of `stageDiagram`, as a cone on
`stageRingDiagram`. -/
def limitObjRingCone (I : Ideal A) (B : AdicAlgebraSystem A I) :
    Cone (stageRingDiagram I B) where
  pt := (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).obj (limitObj I B)
  π.app i :=
    (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).map
      (limit.π (stageDiagram I B) i)
  π.naturality := by
        intro first second transition
        exact limitObjRingCone_naturality I B transition

/-- The canonical ring comparison from the algebra limit to the ring limit. -/
def toRingLimitHom (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).obj (limitObj I B) ⟶
      limit (stageRingDiagram I B) :=
  limit.lift (stageRingDiagram I B) (limitObjRingCone I B)

/-- `toRingLimitHom` is the lift of `limitObjRingCone`. -/
theorem toRingLimitHom_eq (I : Ideal A) (B : AdicAlgebraSystem A I) :
    toRingLimitHom I B =
      limit.lift (stageRingDiagram I B) (limitObjRingCone I B) := by
  rfl

/-- Ring-limit projections respect the coefficient algebra structure. -/
private theorem ringLimitπAlgHom_laws (I : Ideal A) (B : AdicAlgebraSystem A I) (i : OrderDual ℕ+) :
    (((limit.π (stageRingDiagram I B) i).hom) (1 : (limit (stageRingDiagram I B) : CommRingCat.{u})) = (1 : ((stageDiagram I B).obj i))) ∧
    (∀ x y, ((limit.π (stageRingDiagram I B) i).hom) (x * y) = ((limit.π (stageRingDiagram I B) i).hom) x * ((limit.π (stageRingDiagram I B) i).hom) y) ∧
    (((limit.π (stageRingDiagram I B) i).hom) 0 = 0) ∧
    (∀ x y, ((limit.π (stageRingDiagram I B) i).hom) (x + y) = ((limit.π (stageRingDiagram I B) i).hom) x + ((limit.π (stageRingDiagram I B) i).hom) y) ∧
    (∀ a : A, ((limit.π (stageRingDiagram I B) i).hom) (algebraMap A (limit (stageRingDiagram I B) : CommRingCat.{u}) a) = algebraMap A ((stageDiagram I B).obj i) a) := by
  sorry

/-- Projection from the ring limit to a stage, as an `A`-algebra map. -/
def ringLimitπAlgHom (I : Ideal A) (B : AdicAlgebraSystem A I)
    (i : OrderDual ℕ+) :
    (limit (stageRingDiagram I B) : CommRingCat.{u}) →ₐ[A]
      (stageDiagram I B).obj i where
  toFun := (limit.π (stageRingDiagram I B) i).hom
  map_one' := by exact (ringLimitπAlgHom_laws I B i).1
  map_mul' := by exact (ringLimitπAlgHom_laws I B i).2.1
  map_zero' := by exact (ringLimitπAlgHom_laws I B i).2.2.1
  map_add' := by exact (ringLimitπAlgHom_laws I B i).2.2.2.1
  commutes' := by exact (ringLimitπAlgHom_laws I B i).2.2.2.2

/-- Unfolding of `ringLimitπAlgHom` as the underlying ring-limit
projection. -/
theorem ringLimitπAlgHom_toFun (I : Ideal A) (B : AdicAlgebraSystem A I)
    (i : OrderDual ℕ+) (x : (limit (stageRingDiagram I B) : CommRingCat.{u})) :
    ringLimitπAlgHom I B i x = (limit.π (stageRingDiagram I B) i).hom x := by
  rfl

/-- The algebra-valued ring-limit projections form a compatible cone. -/
private theorem ringLimitAlgebraCone_naturality (I : Ideal A) (B : AdicAlgebraSystem A I) :
    ∀ {i j : OrderDual ℕ+} (f : i ⟶ j),
      ((Functor.const (OrderDual ℕ+)).obj (CommAlgCat.of A (limit (stageRingDiagram I B) : CommRingCat.{u}))).map f ≫
        CommAlgCat.ofHom (ringLimitπAlgHom I B j) = CommAlgCat.ofHom (ringLimitπAlgHom I B i) ≫ (stageDiagram I B).map f := by
  sorry

/-- The ring limit, viewed as an `A`-algebra, as a cone on `stageDiagram`. -/
def ringLimitAlgebraCone (I : Ideal A) (B : AdicAlgebraSystem A I) :
    Cone (stageDiagram I B) where
  pt := CommAlgCat.of A (limit (stageRingDiagram I B) : CommRingCat.{u})
  π.app i := CommAlgCat.ofHom (ringLimitπAlgHom I B i)
  π.naturality := by
        intro first second transition
        exact ringLimitAlgebraCone_naturality I B transition

/-- The canonical `A`-algebra comparison from the ring limit to the algebra
limit. -/
def fromRingLimitAlgHom (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (limit (stageRingDiagram I B) : CommRingCat.{u}) →ₐ[A] limitObj I B :=
  (limit.lift (stageDiagram I B) (ringLimitAlgebraCone I B)).hom

/-- `fromRingLimitAlgHom` is the lift of `ringLimitAlgebraCone`. -/
theorem fromRingLimitAlgHom_eq (I : Ideal A) (B : AdicAlgebraSystem A I) :
    fromRingLimitAlgHom I B =
      (limit.lift (stageDiagram I B) (ringLimitAlgebraCone I B)).hom := by
  rfl

/-- The forgotten algebra-limit projections form a compatible cone. -/
private theorem limitObjModuleCone_naturality (I : Ideal A) (B : AdicAlgebraSystem A I) :
    ∀ {i j : OrderDual ℕ+} (f : i ⟶ j),
      ((Functor.const (OrderDual ℕ+)).obj (ModuleCat.of A (limitObj I B))).map f ≫
        (CommAlgCat.forgetToModule A).map (limit.π (stageDiagram I B) j) =
      (CommAlgCat.forgetToModule A).map (limit.π (stageDiagram I B) i) ≫
        (stageModuleDiagram I B).map f := by
  sorry

/-- The forgotten limit cone of `stageDiagram`, as a cone on
`stageModuleDiagram`. -/
def limitObjModuleCone (I : Ideal A) (B : AdicAlgebraSystem A I) :
    Cone (stageModuleDiagram I B) where
  pt := ModuleCat.of A (limitObj I B)
  π.app i :=
    (CommAlgCat.forgetToModule A).map (limit.π (stageDiagram I B) i)
  π.naturality := by
        intro first second transition
        exact limitObjModuleCone_naturality I B transition

/-- The canonical `A`-linear comparison from the algebra limit to the module
limit. -/
def toModuleLimitLinearMap (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (limitObj I B : Type u) →ₗ[A]
      (limit (stageModuleDiagram I B) : ModuleCat A) :=
  (limit.lift (stageModuleDiagram I B) (limitObjModuleCone I B)).hom

/-- `toModuleLimitLinearMap` is the lift of `limitObjModuleCone`. -/
theorem toModuleLimitLinearMap_eq (I : Ideal A) (B : AdicAlgebraSystem A I) :
    toModuleLimitLinearMap I B =
      (limit.lift (stageModuleDiagram I B) (limitObjModuleCone I B)).hom := by
  rfl

/-- The stagewise identifications of underlying module and ring carriers are natural. -/
private theorem stageForgetNatIso_naturality (I : Ideal A) (B : AdicAlgebraSystem A I) :
    let app := (fun i ↦
      eqToIso <|
        Eq.trans
          (rfl :
            (stageModuleDiagram I B ⋙ forget (ModuleCat.{u} A)).obj i =
              ((stageDiagram I B).obj i : Type u))
          (Eq.symm
            (rfl :
              (stageRingDiagram I B ⋙ forget CommRingCat.{u}).obj i =
                ((stageDiagram I B).obj i : Type u))))
    ∀ {i j : OrderDual ℕ+} (f : i ⟶ j),
      (stageModuleDiagram I B ⋙ forget (ModuleCat.{u} A)).map f ≫ (app j).hom =
        (app i).hom ≫ (stageRingDiagram I B ⋙ forget CommRingCat.{u}).map f := by
  sorry

/-- The Type-valued diagrams of `stageModuleDiagram` and `stageRingDiagram`
are canonically isomorphic. -/
def stageForgetNatIso (I : Ideal A) (B : AdicAlgebraSystem A I) :
    stageModuleDiagram I B ⋙ forget (ModuleCat.{u} A) ≅
      stageRingDiagram I B ⋙ forget CommRingCat.{u} :=
  NatIso.ofComponents
    (fun i ↦
      eqToIso <|
        Eq.trans
          (rfl :
            (stageModuleDiagram I B ⋙ forget (ModuleCat.{u} A)).obj i =
              ((stageDiagram I B).obj i : Type u))
          (Eq.symm
            (rfl :
              (stageRingDiagram I B ⋙ forget CommRingCat.{u}).obj i =
                ((stageDiagram I B).obj i : Type u))))
    (by
      intro first second transition
      exact stageForgetNatIso_naturality I B transition)

/-- Canonical module-limit and ring-limit comparison composites are mutually inverse. -/
private theorem moduleLimitToRingLimitEquiv_laws (I : Ideal A) (B : AdicAlgebraSystem A I) :
    let forward := (preservesLimitIso (forget CommRingCat.{u}) (stageRingDiagram I B)).inv ∘
        (HasLimit.isoOfNatIso (stageForgetNatIso I B)).hom ∘
          (preservesLimitIso (forget (ModuleCat.{u} A))
              (stageModuleDiagram I B)).hom
    let backward := (preservesLimitIso (forget (ModuleCat.{u} A))
            (stageModuleDiagram I B)).inv ∘
        (HasLimit.isoOfNatIso (stageForgetNatIso I B)).inv ∘
          (preservesLimitIso (forget CommRingCat.{u})
              (stageRingDiagram I B)).hom
    Function.LeftInverse backward forward ∧ Function.RightInverse backward forward := by
  sorry

/-- Named Type-identification of the module limit with the ring limit. -/
def moduleLimitToRingLimitEquiv (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (limit (stageModuleDiagram I B) : ModuleCat A) ≃
      (limit (stageRingDiagram I B) : CommRingCat.{u}) :=
  { toFun :=
      (preservesLimitIso (forget CommRingCat.{u}) (stageRingDiagram I B)).inv ∘
        (HasLimit.isoOfNatIso (stageForgetNatIso I B)).hom ∘
          (preservesLimitIso (forget (ModuleCat.{u} A))
              (stageModuleDiagram I B)).hom
    invFun :=
      (preservesLimitIso (forget (ModuleCat.{u} A))
            (stageModuleDiagram I B)).inv ∘
        (HasLimit.isoOfNatIso (stageForgetNatIso I B)).inv ∘
          (preservesLimitIso (forget CommRingCat.{u})
              (stageRingDiagram I B)).hom
    left_inv := by exact (moduleLimitToRingLimitEquiv_laws I B).1
    right_inv := by exact (moduleLimitToRingLimitEquiv_laws I B).2 }

/-- The inverse comparison from the module limit to the algebra limit. -/
def fromModuleLimit (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (limit (stageModuleDiagram I B) : ModuleCat A) → limitObj I B :=
  fun x ↦ fromRingLimitAlgHom I B (moduleLimitToRingLimitEquiv I B x)

/-- `fromModuleLimit` factors through `fromRingLimitAlgHom`. -/
theorem fromModuleLimit_eq (I : Ideal A) (B : AdicAlgebraSystem A I)
    (x : (limit (stageModuleDiagram I B) : ModuleCat A)) :
    fromModuleLimit I B x =
      fromRingLimitAlgHom I B (moduleLimitToRingLimitEquiv I B x) := by
  rfl

/-- The explicit module-limit comparison and its inverse are mutually inverse. -/
private theorem limitObjModuleLinearEquiv_laws (I : Ideal A) (B : AdicAlgebraSystem A I) :
    Function.LeftInverse (fromModuleLimit I B) (toModuleLimitLinearMap I B) ∧
    Function.RightInverse (fromModuleLimit I B) (toModuleLimitLinearMap I B) := by
  sorry

/-- Named identification of the inverse limit in `CommAlgCat` with the inverse
limit of the underlying `A`-module diagram. -/
def limitObjModuleLinearEquiv (I : Ideal A) (B : AdicAlgebraSystem A I) :
    (limitObj I B : Type u) ≃ₗ[A]
      (limit (stageModuleDiagram I B) : ModuleCat A) :=
  { toModuleLimitLinearMap I B with
    invFun := fromModuleLimit I B
    left_inv := by exact (limitObjModuleLinearEquiv_laws I B).1
    right_inv := by exact (limitObjModuleLinearEquiv_laws I B).2 }

/-- The forward map of `limitObjModuleLinearEquiv` is
`toModuleLimitLinearMap`. -/
theorem limitObjModuleLinearEquiv_apply (I : Ideal A)
    (B : AdicAlgebraSystem A I) (x : limitObj I B) :
    limitObjModuleLinearEquiv I B x = toModuleLimitLinearMap I B x := by
  rfl

/-- Named identification of the extended power `(I ^ n).map (algebraMap A B)`
with the submodule `I ^ n • ⊤`, after restriction of scalars to `A`. -/
private theorem map_pow_restrictScalars_eq_smul_top (I : Ideal A) (B : Type u)
    [CommRing B] [Algebra A B] (n : ℕ) :
    ((I ^ n).map (algebraMap A B)).restrictScalars A =
      I ^ n • (⊤ : Submodule A B) :=
  sorry

/-- Successor maps of `stageModuleDiagram` are surjective. -/
theorem stageModuleDiagram_stepSurjective (I : Ideal A)
    (B : AdicAlgebraSystem A I) :
    ∀ n : ℕ+, Function.Surjective ((stageModuleDiagram I B).stepLinearMap n) := by
  intro n x
  obtain ⟨q, hq⟩ := (B.property.bijective_stepQuotientHom n).surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨y, hq⟩

/-- The kernel of a successor map of `stageModuleDiagram` is `I ^ n • ⊤`. -/
theorem stageModuleDiagram_ker_stepLinearMap (I : Ideal A)
    (B : AdicAlgebraSystem A I) :
    ∀ n : ℕ+,
      LinearMap.ker ((stageModuleDiagram I B).stepLinearMap n) =
        I ^ (n : ℕ) •
          (⊤ : Submodule A ((stageModuleDiagram I B).stage (n + 1))) :=
  sorry

/-- Limit projections annihilate the extended ideal power and descend as algebra maps. -/
private theorem limitQuotientToStageAlgHom_laws (I : Ideal A) (B : AdicAlgebraSystem A I) (n : ℕ+) :
    (∀ x : limitObj I B, x ∈ (I ^ (n : ℕ)).map (algebraMap A (limitObj I B)) →
      ((limit.π (stageDiagram I B) (OrderDual.toDual n)).hom.toRingHom) x = 0) ∧
    (∀ h : ∀ x : limitObj I B, x ∈ (I ^ (n : ℕ)).map (algebraMap A (limitObj I B)) →
      ((limit.π (stageDiagram I B) (OrderDual.toDual n)).hom.toRingHom) x = 0,
      ∀ a : A, (Ideal.Quotient.lift ((I ^ (n : ℕ)).map (algebraMap A (limitObj I B)))
          ((limit.π (stageDiagram I B) (OrderDual.toDual n)).hom.toRingHom) h)
        (algebraMap A (limitObj I B ⧸ (I ^ (n : ℕ)).map (algebraMap A (limitObj I B))) a) =
          algebraMap A (B.obj.right.stage n) a) := by
  sorry

/-- The descended limit projection `(lim B m) ⧸ I ^ n (lim B m) ⟶ B n`. -/
def limitQuotientToStageAlgHom (I : Ideal A) (B : AdicAlgebraSystem A I)
    (n : ℕ+) :
    (limitObj I B ⧸ (I ^ (n : ℕ)).map (algebraMap A (limitObj I B))) →ₐ[A]
      B.obj.right.stage n where
  toRingHom :=
    Ideal.Quotient.lift ((I ^ (n : ℕ)).map (algebraMap A (limitObj I B)))
      (limit.π (stageDiagram I B) (OrderDual.toDual n)).hom.toRingHom
      (by exact (limitQuotientToStageAlgHom_laws I B n).1)
  commutes' := by
    exact (limitQuotientToStageAlgHom_laws I B n).2
      (limitQuotientToStageAlgHom_laws I B n).1

/-- The algebra-to-module limit equivalence transports extended ideal-power submodules. -/
private theorem limitObjQuotientToModuleQuotient_law (I : Ideal A) (B : AdicAlgebraSystem A I) (n : ℕ+) :
    Submodule.map (limitObjModuleLinearEquiv I B).toLinearMap
      (I ^ (n : ℕ) • (⊤ : Submodule A (limitObj I B))) =
      I ^ (n : ℕ) • (⊤ : Submodule A (limit (stageModuleDiagram I B) : ModuleCat A)) := by
  sorry

/-- Named identification of the algebra-limit quotient by the extended power
of `I` with the module-limit quotient by `I ^ n • ⊤`. -/
def limitObjQuotientToModuleQuotient (I : Ideal A)
    (B : AdicAlgebraSystem A I) (n : ℕ+) :
    (limitObj I B ⧸ (I ^ (n : ℕ)).map (algebraMap A (limitObj I B))) ≃ₗ[A]
      ((limit (stageModuleDiagram I B) : ModuleCat A) ⧸
        I ^ (n : ℕ) •
          (⊤ : Submodule A
            (limit (stageModuleDiagram I B) : ModuleCat A))) :=
  ((Submodule.Quotient.restrictScalarsEquiv A
          ((I ^ (n : ℕ)).map (algebraMap A (limitObj I B)))).symm.trans
      (Submodule.quotEquivOfEq _ _
        (by exact map_pow_restrictScalars_eq_smul_top I (limitObj I B) n))).trans
    (Submodule.Quotient.equiv
      (I ^ (n : ℕ) • (⊤ : Submodule A (limitObj I B)))
      (I ^ (n : ℕ) •
        (⊤ : Submodule A (limit (stageModuleDiagram I B) : ModuleCat A)))
      (limitObjModuleLinearEquiv I B) (by exact limitObjQuotientToModuleQuotient_law I B n))

/-- The inverse module quotient comparison preserves one and multiplication. -/
private theorem stageToLimitQuotientAlgHom_laws (I : Ideal A) (hI : I.FG) (B : AdicAlgebraSystem A I) (n : ℕ+) :
    let comparison := ((limitObjQuotientToModuleQuotient I B n).symm.toLinearMap.comp
      ((stageModuleDiagram I B).limitProjectionQuotientEquiv I hI
          (stageModuleDiagram_stepSurjective I B)
          (stageModuleDiagram_ker_stepLinearMap I B) n).symm.toLinearMap)
    comparison (1 : B.obj.right.stage n) = 1 ∧
      ∀ x y : B.obj.right.stage n, comparison (x * y) = comparison x * comparison y := by
  sorry

/-- The inverse comparison `B n ⟶ (lim B m) ⧸ I ^ n (lim B m)`, obtained from
the inverse of `limitProjectionQuotientEquiv` after the named limit and ideal
identifications. -/
def stageToLimitQuotientAlgHom (I : Ideal A) (hI : I.FG)
    (B : AdicAlgebraSystem A I) (n : ℕ+) :
    B.obj.right.stage n →ₐ[A]
      limitObj I B ⧸ (I ^ (n : ℕ)).map (algebraMap A (limitObj I B)) :=
  AlgHom.ofLinearMap
    ((limitObjQuotientToModuleQuotient I B n).symm.toLinearMap.comp
      ((stageModuleDiagram I B).limitProjectionQuotientEquiv I hI
          (stageModuleDiagram_stepSurjective I B)
          (stageModuleDiagram_ker_stepLinearMap I B) n).symm.toLinearMap)
    (by exact (stageToLimitQuotientAlgHom_laws I hI B n).1)
    (by exact (stageToLimitQuotientAlgHom_laws I hI B n).2)

/-- The canonical stage comparison and inverse quotient comparison are mutually inverse. -/
private theorem limitObjQuotientAlgEquiv_laws (I : Ideal A) (hI : I.FG) (B : AdicAlgebraSystem A I) (n : ℕ+) :
    (limitQuotientToStageAlgHom I B n).comp (stageToLimitQuotientAlgHom I hI B n) =
      AlgHom.id A _ ∧
    (stageToLimitQuotientAlgHom I hI B n).comp (limitQuotientToStageAlgHom I B n) =
      AlgHom.id A _ := by
  sorry

/-- The canonical algebra equivalence
`(lim B m) ⧸ I ^ n (lim B m) ≃ₐ[A] B n`, for finitely generated `I`. -/
def limitObjQuotientAlgEquiv (I : Ideal A) (hI : I.FG)
    (B : AdicAlgebraSystem A I) (n : ℕ+) :
    (limitObj I B ⧸ (I ^ (n : ℕ)).map (algebraMap A (limitObj I B))) ≃ₐ[A]
      B.obj.right.stage n :=
  AlgEquiv.ofAlgHom (limitQuotientToStageAlgHom I B n)
    (stageToLimitQuotientAlgHom I hI B n) (by exact (limitObjQuotientAlgEquiv_laws I hI B n).1)
    (by exact (limitObjQuotientAlgEquiv_laws I hI B n).2)

/-- Canonical reconstruction comparison components are natural. -/
private theorem limitFunctorCounitRightIso_naturality (I : Ideal A) (hI : I.FG) (B : AdicAlgebraSystem A I) :
    let app := (fun i ↦
      RingEquiv.toCommRingCatIso
        (limitObjQuotientAlgEquiv I hI B (OrderDual.ofDual i)).toRingEquiv)
    ∀ {X Y} (f : X ⟶ Y),
      (((limitFunctor I hI ⋙ CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B).obj.right).map f ≫ (app Y).hom = (app X).hom ≫ (B.obj.right).map f := by
  sorry

/-- The right-leg isomorphism of inverse systems underlying the counit
comparison. -/
def limitFunctorCounitRightIso (I : Ideal A) (hI : I.FG)
    (B : AdicAlgebraSystem A I) :
    ((limitFunctor I hI ⋙
          CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B).obj.right ≅
      B.obj.right :=
  NatIso.ofComponents
    (fun i ↦
      RingEquiv.toCommRingCatIso
        (limitObjQuotientAlgEquiv I hI B (OrderDual.ofDual i)).toRingEquiv)
    (by exact limitFunctorCounitRightIso_naturality I hI B)

/-- Canonical reconstruction comparison components are natural. -/
private theorem limitFunctorUnitIso_naturality (I : Ideal A) (hI : I.FG) :
    let app := (fun B ↦
      CommAlgCat.TopologicallyFiniteType.isoMk (completeLimitAlgEquiv I hI B))
    ∀ {X Y} (f : X ⟶ Y),
      (𝟭 (CommAlgCat.TopologicallyFiniteType.{u} A I)).map f ≫ (app Y).hom = (app X).hom ≫ (CommAlgCat.TopologicallyFiniteType.toAdicSystem I ⋙ limitFunctor I hI).map f := by
  sorry

/-- The unit isomorphism from the identity to quotient-system reconstruction. -/
def limitFunctorUnitIso (I : Ideal A) (hI : I.FG) :
    𝟭 (CommAlgCat.TopologicallyFiniteType.{u} A I) ≅
      CommAlgCat.TopologicallyFiniteType.toAdicSystem I ⋙ limitFunctor I hI :=
  NatIso.ofComponents
    (fun B ↦
      CommAlgCat.TopologicallyFiniteType.isoMk (completeLimitAlgEquiv I hI B))
    (by exact limitFunctorUnitIso_naturality I hI)

/-- The stagewise counit respects coefficient-system maps and is natural in adic systems. -/
private theorem limitFunctorCounitIso_laws (I : Ideal A) (hI : I.FG) :
    (∀ B : AdicAlgebraSystem A I,
      ((limitFunctor I hI ⋙ CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B).obj.hom ≫
        (limitFunctorCounitRightIso I hI B).hom = B.obj.hom) ∧
    (∀ h : ∀ B : AdicAlgebraSystem A I,
      ((limitFunctor I hI ⋙ CommAlgCat.TopologicallyFiniteType.toAdicSystem I).obj B).obj.hom ≫
        (limitFunctorCounitRightIso I hI B).hom = B.obj.hom,
      let app := (fun B ↦ ObjectProperty.isoMk _
        (Under.isoMk (limitFunctorCounitRightIso I hI B) (h B)))
      ∀ {X Y : AdicAlgebraSystem A I} (f : X ⟶ Y),
        (limitFunctor I hI ⋙ CommAlgCat.TopologicallyFiniteType.toAdicSystem I).map f ≫
          (app Y).hom = (app X).hom ≫ f) := by
  sorry

/-- The counit isomorphism from reconstructed quotient systems to the identity. -/
def limitFunctorCounitIso (I : Ideal A) (hI : I.FG) :
    limitFunctor I hI ⋙ CommAlgCat.TopologicallyFiniteType.toAdicSystem I ≅
      𝟭 (AdicAlgebraSystem A I) :=
  NatIso.ofComponents
    (fun B ↦
      ObjectProperty.isoMk _
        (Under.isoMk (limitFunctorCounitRightIso I hI B) ((by exact (limitFunctorCounitIso_laws I hI).1 B))))
    (by exact (limitFunctorCounitIso_laws I hI).2 (limitFunctorCounitIso_laws I hI).1)

/-- Explicit quasi-inverse data for `toAdicSystem`, with inverse the
inverse-limit functor. -/
def limitFunctorQuasiInverse (I : Ideal A) (hI : I.FG) :
    (CommAlgCat.TopologicallyFiniteType.toAdicSystem I).QuasiInverse where
  inverse := limitFunctor I hI
  unitIso := limitFunctorUnitIso I hI
  counitIso := limitFunctorCounitIso I hI

/-- The inverse stored by `limitFunctorQuasiInverse` is `limitFunctor`. -/
theorem limitFunctorQuasiInverse_inverse (I : Ideal A) (hI : I.FG) :
    (limitFunctorQuasiInverse I hI).inverse = limitFunctor I hI := by
  rfl

/-- `limitFunctor` is a quasi-inverse of `toAdicSystem`. -/
theorem limitFunctor_isQuasiInverse (I : Ideal A) (hI : I.FG) :
    (limitFunctor I hI).IsQuasiInverse
      (CommAlgCat.TopologicallyFiniteType.toAdicSystem I) :=
  ⟨⟨(limitFunctorCounitIso I hI).symm⟩, ⟨(limitFunctorUnitIso I hI).symm⟩⟩

/-- The equivalence between finite-type adic systems and topologically finite type algebras induced by the inverse-limit functor and
`toAdicSystem`. -/
def limitFunctorEquivalence (I : Ideal A) (hI : I.FG) :
    AdicAlgebraSystem A I ≌ CommAlgCat.TopologicallyFiniteType.{u} A I :=
  CategoryTheory.Equivalence.mk (limitFunctor I hI)
    (CommAlgCat.TopologicallyFiniteType.toAdicSystem I)
    (limitFunctorCounitIso I hI).symm (limitFunctorUnitIso I hI).symm

end AdicAlgebraSystem
