/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.Category
public import ReasLib.Algebra.DirectSum.NatToInt
public import ReasLib.Algebra.Module.Graded.Reindex
public import ReasLib.Algebra.Module.Graded.Decomposition
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Sections
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GlobalSections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated twisted sections

The integral twists of a module on a projective spectrum assemble into a graded module.  This
file keeps the underlying maps explicit and records their algebraic laws separately.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj.TwistedSections

section IntegralBase

variable {R : Type v} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

namespace Integral

/-- The degree-`n` integral twisted global sections of `F`. -/
abbrev degree (F : (Proj 𝒜).Modules) (n : ℤ) : Type u :=
  Γ(ProjTwistFamily.tensorTwist
    (AssociatedModule.twistingSheaf (R := R) (A := A) 𝒜) F n, ⊤)

end Integral

/-- Multiplication by `p` sends the shift by `n` into the shift by `(m : ℤ) + n`. -/
theorem mulMapsTo {m : ℕ} (p : 𝒜 m) (n i : ℤ) (g : A)
    (hg : g ∈ GradedModule.shiftGrading
      (DirectSum.Decomposition.natToIntGrading 𝒜) n i) :
    LinearMap.mulLeft A p.1 g ∈ GradedModule.shiftGrading
      (DirectSum.Decomposition.natToIntGrading 𝒜) ((m : ℤ) + n) i := sorry

/-- The morphism of twisting sheaves induced by multiplication by a homogeneous element. -/
@[stacks 0BXF, stacks 01CV "homogeneous multiplication between twisting sheaves"]
noncomputable def twistMap {m : ℕ} (p : 𝒜 m) (n : ℤ) :
    AssociatedModule.twistingSheaf (R := R) (A := A) 𝒜 n ⟶
      AssociatedModule.twistingSheaf (R := R) (A := A) 𝒜 ((m : ℤ) + n) :=
  AssociatedModule.map
    (𝒜 := 𝒜)
    (ℳ := GradedModule.shiftGrading
      (DirectSum.Decomposition.natToIntGrading 𝒜) n)
    (ℵ := GradedModule.shiftGrading
      (DirectSum.Decomposition.natToIntGrading 𝒜) ((m : ℤ) + n))
    (φ := LinearMap.mulLeft A p.1)
    (hφ := mulMapsTo 𝒜 p n)

/-- Tensoring `F` with the twist multiplication map. -/
@[stacks 0BXF, stacks 01CV "tensor twist multiplication map"]
noncomputable def actionMap (F : (Proj 𝒜).Modules) {m : ℕ} (p : 𝒜 m) (n : ℤ) :
    tensorObj F (AssociatedModule.twistingSheaf (R := R) (A := A) 𝒜 n) ⟶
      tensorObj F (AssociatedModule.twistingSheaf (R := R) (A := A) 𝒜 ((m : ℤ) + n)) :=
  𝟙 F ⊗ₘ twistMap 𝒜 p n

namespace Integral

/-- The homogeneous action on integral twisted global sections. -/
@[stacks 0BXF, stacks 01CV "homogeneous action on twisted global sections"]
noncomputable def smul (F : (Proj 𝒜).Modules) {m : ℕ} {n : ℤ}
    (p : 𝒜 m) (x : degree 𝒜 F n) : degree 𝒜 F ((m : ℤ) + n) :=
  (Scheme.Modules.globalSectionsMap (actionMap 𝒜 F p n)).hom x

/-- Integral twisted sections have their explicit graded scalar multiplication. -/
noncomputable instance instGSMul (F : (Proj 𝒜).Modules) :
    GradedMonoid.GSMul (fun m : ℕ ↦ 𝒜 m) (degree 𝒜 F) where
  smul := fun p x ↦ smul 𝒜 F p x

/-- The degree-zero unit acts trivially on integral twisted sections. -/
theorem one_smul (F : (Proj 𝒜).Modules) (x : GradedMonoid (degree 𝒜 F)) :
    (1 : GradedMonoid (fun m : ℕ ↦ 𝒜 m)) • x = x := sorry

/-- Successive homogeneous actions compose as multiplication. -/
theorem mul_smul (F : (Proj 𝒜).Modules)
    (a b : GradedMonoid (fun m : ℕ ↦ 𝒜 m)) (x : GradedMonoid (degree 𝒜 F)) :
    (a * b) • x = a • b • x := sorry

/-- A homogeneous scalar distributes over addition of integral twisted sections. -/
theorem smul_add (F : (Proj 𝒜).Modules) {m : ℕ} {n : ℤ}
    (p : 𝒜 m) (x y : degree 𝒜 F n) :
    smul 𝒜 F p (x + y) = smul 𝒜 F p x + smul 𝒜 F p y := sorry

/-- A homogeneous scalar sends zero integral twisted section to zero. -/
theorem smul_zero (F : (Proj 𝒜).Modules) {m : ℕ} {n : ℤ} (p : 𝒜 m) :
    smul 𝒜 F p (0 : degree 𝒜 F n) = 0 := sorry

/-- Addition of homogeneous scalars distributes through the integral action. -/
theorem add_smul (F : (Proj 𝒜).Modules) {m : ℕ} {n : ℤ}
    (p q : 𝒜 m) (x : degree 𝒜 F n) :
    smul 𝒜 F (p + q) x = smul 𝒜 F p x + smul 𝒜 F q x := sorry

/-- The zero homogeneous scalar acts by zero on integral twisted sections. -/
theorem zero_smul (F : (Proj 𝒜).Modules) {m : ℕ} {n : ℤ} (x : degree 𝒜 F n) :
    smul 𝒜 F (0 : 𝒜 m) x = 0 := sorry

/-- Integral twisted sections form a graded multiplicative action. -/
noncomputable instance instGMulAction (F : (Proj 𝒜).Modules) :
    GradedMonoid.GMulAction (fun m : ℕ ↦ 𝒜 m) (degree 𝒜 F) where
  one_smul := one_smul 𝒜 F
  mul_smul := mul_smul 𝒜 F

/-- Integral twisted sections form a graded distributive multiplicative action. -/
noncomputable instance instGdistribMulAction (F : (Proj 𝒜).Modules) :
    DirectSum.GdistribMulAction (fun m : ℕ ↦ 𝒜 m) (degree 𝒜 F) where
  smul_add := smul_add 𝒜 F
  smul_zero := smul_zero 𝒜 F

/-- Integral twisted sections form a graded module over `𝒜`. -/
noncomputable instance instGmodule (F : (Proj 𝒜).Modules) :
    DirectSum.Gmodule (fun m : ℕ ↦ 𝒜 m) (degree 𝒜 F) where
  add_smul := add_smul 𝒜 F
  zero_smul := zero_smul 𝒜 F

end Integral

namespace Integral

/-- The map on one integral twisted-section degree induced by `f`. -/
noncomputable def mapDegree {F G : (Proj 𝒜).Modules} (f : F ⟶ G) (n : ℤ) :
    degree 𝒜 F n →+ degree 𝒜 G n :=
  (Scheme.Modules.globalSectionsMap
    (f ⊗ₘ 𝟙 (AssociatedModule.twistingSheaf (R := R) (A := A) 𝒜 n))).hom

end Integral

end IntegralBase

section NonnegativeBase

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

namespace Nonnegative

/-- The nonnegative degree-`n` piece of twisted sections. -/
abbrev degree (F : (Proj 𝒜).Modules) (n : ℕ) : Type u :=
  Integral.degree 𝒜 F (n : ℤ)

/-- The direct sum of the nonnegative twisted-section pieces. -/
abbrev carrier (F : (Proj 𝒜).Modules) : Type u :=
  ⨁ n : ℕ, degree 𝒜 F n

/-- The integer grading on the nonnegative twisted-section direct sum. -/
abbrev grading (F : (Proj 𝒜).Modules) : ℤ → Submodule ℤ (carrier 𝒜 F) :=
  DirectSum.natToIntGrading (R := ℤ) (degree 𝒜 F)

/-- 0BXF: Nonnegative twisted sections form the graded module obtained by reindexing the
integral twisted-section action along the canonical inclusion `ℕ → ℤ`. -/
@[stacks 0BXF]
noncomputable instance instGmodule (F : (Proj 𝒜).Modules) :
    DirectSum.Gmodule (fun m : ℕ ↦ 𝒜 m) (degree 𝒜 F) :=
  DirectSum.Gmodule.reindex AddAction.natIntHom (Integral.degree 𝒜 F)

/-- The reindexed homogeneous action is the integral action transported along `Nat.cast_add`. -/
theorem gsmul_eq_integral_smul (F : (Proj 𝒜).Modules) {m n : ℕ}
    (p : 𝒜 m) (x : degree 𝒜 F n) :
    GradedMonoid.GSMul.smul (A := fun i : ℕ ↦ 𝒜 i) (M := degree 𝒜 F) p x =
      Eq.mp (congrArg (Integral.degree 𝒜 F) (Nat.cast_add m n)).symm
        (Integral.smul 𝒜 F p x) := sorry

/-- The module over `A` induced from the graded direct-sum action. -/
noncomputable instance instModule (F : (Proj 𝒜).Modules) : Module A (carrier 𝒜 F) :=
  DirectSum.Gmodule.moduleOfDecomposition 𝒜 (degree 𝒜 F)

/-- The induced `A`-action on pure summands is the homogeneous twisted-section action. -/
theorem smul_of (F : (Proj 𝒜).Modules) {m n : ℕ}
    (p : 𝒜 m) (x : degree 𝒜 F n) :
    (p : A) • DirectSum.of (degree 𝒜 F) n x =
      DirectSum.of (degree 𝒜 F) (m + n)
        (GradedMonoid.GSMul.smul (A := fun i : ℕ ↦ 𝒜 i) (M := degree 𝒜 F) p x) := sorry

/-- The induced `A`-action agrees with the base `ℤ`-module structure. -/
theorem isScalarTower (F : (Proj 𝒜).Modules) :
    IsScalarTower ℤ A (carrier 𝒜 F) := sorry

/-- The induced action of a homogeneous scalar preserves the translated direct-sum grading. -/
theorem smulMem (F : (Proj 𝒜).Modules) {m : ℕ} {n : ℤ}
    {p : A} (hp : p ∈ 𝒜 m) {x : carrier 𝒜 F} (hx : x ∈ grading 𝒜 F n) :
    p • x ∈ grading 𝒜 F ((m : ℤ) + n) := sorry

/-- The direct-sum grading is compatible with the induced `A`-action. -/
noncomputable instance instGradedSMul (F : (Proj 𝒜).Modules) :
    SetLike.GradedSMul 𝒜 (grading 𝒜 F) where
  smul_mem := fun {i} {j} {a} {x} ha hx ↦
    smulMem 𝒜 F (m := i) (n := j) (p := a) (x := x) ha hx

/-- The twisted sections of `F`, bundled as an integer-graded left `𝒜`-module. -/
@[stacks 0BXF]
noncomputable def obj (F : (Proj 𝒜).Modules) : GradedModule.Left 𝒜 ℤ where
  carrier := carrier 𝒜 F
  moduleAlgebra := instModule 𝒜 F
  isScalarTower := isScalarTower 𝒜 F
  grading := grading 𝒜 F
  decomposition := DirectSum.natToIntGradingDecomposition (R := ℤ) (degree 𝒜 F)
  gradedSMul := instGradedSMul 𝒜 F

/-- The map on one nonnegative twisted-section degree induced by `f`. -/
noncomputable def degreeMap {F G : (Proj 𝒜).Modules} (f : F ⟶ G) (n : ℕ) :
    degree 𝒜 F n →+ degree 𝒜 G n :=
  Integral.mapDegree 𝒜 f (n : ℤ)

/-- The additive map on nonnegative direct sums induced degreewise by `f`. -/
noncomputable def mapAddHom {F G : (Proj 𝒜).Modules} (f : F ⟶ G) :
    carrier 𝒜 F →+ carrier 𝒜 G :=
  DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (degree 𝒜 G) n).comp (degreeMap 𝒜 f n)

/-- The componentwise direct-sum map has the expected value on a pure summand. -/
theorem mapAddHom_of {F G : (Proj 𝒜).Modules} (f : F ⟶ G)
    (n : ℕ) (x : degree 𝒜 F n) :
    mapAddHom 𝒜 f (DirectSum.of (degree 𝒜 F) n x) =
      DirectSum.of (degree 𝒜 G) n (degreeMap 𝒜 f n x) := sorry

/-- The componentwise direct-sum map is compatible with the induced `A`-actions. -/
theorem map_smul {F G : (Proj 𝒜).Modules} (f : F ⟶ G)
    (a : A) (x : carrier 𝒜 F) :
    mapAddHom 𝒜 f (a • x) = a • mapAddHom 𝒜 f x := sorry

/-- The componentwise direct-sum map as an `A`-linear map. -/
noncomputable def mapLinear {F G : (Proj 𝒜).Modules} (f : F ⟶ G) :
    carrier 𝒜 F →ₗ[A] carrier 𝒜 G where
  toFun := mapAddHom 𝒜 f
  map_add' := (mapAddHom 𝒜 f).map_add
  map_smul' := map_smul 𝒜 f

/-- The componentwise map preserves each integer component of the direct-sum grading. -/
theorem map_mem {F G : (Proj 𝒜).Modules} (f : F ⟶ G)
    (n : ℤ) (x : carrier 𝒜 F) (hx : x ∈ grading 𝒜 F n) :
    mapLinear 𝒜 f x ∈ grading 𝒜 G n := sorry

/-- The graded morphism on twisted sections induced by a module morphism. -/
@[stacks 0BXF]
noncomputable def map {F G : (Proj 𝒜).Modules} (f : F ⟶ G) :
    obj 𝒜 F ⟶ obj 𝒜 G :=
  GradedModule.Left.Hom.ofLinearMap (mapLinear 𝒜 f) (map_mem 𝒜 f)

/-- The graded map has the expected value on a pure nonnegative summand. -/
theorem map_of {F G : (Proj 𝒜).Modules} (f : F ⟶ G)
    (n : ℕ) (x : degree 𝒜 F n) :
    GradedModule.Left.Hom.toLinearMap (map 𝒜 f)
      (DirectSum.of (degree 𝒜 F) n x) =
        DirectSum.of (degree 𝒜 G) n (degreeMap 𝒜 f n x) := sorry

/-- The graded map induced by the identity module morphism is the identity. -/
theorem map_id (F : (Proj 𝒜).Modules) :
    map 𝒜 (𝟙 F) = 𝟙 (obj 𝒜 F) := sorry

/-- The graded map induced by a composite is the composite of the graded maps. -/
theorem map_comp {F G H : (Proj 𝒜).Modules} (f : F ⟶ G) (g : G ⟶ H) :
    map 𝒜 (f ≫ g) = map 𝒜 f ≫ map 𝒜 g := sorry

/-- 0BXF: Twisted sections as a functor to integer-graded left modules. -/
@[stacks 0BXF]
noncomputable def functor : (Proj 𝒜).Modules ⥤ GradedModule.Left 𝒜 ℤ where
  obj := obj 𝒜
  map := map 𝒜
  map_id := map_id 𝒜
  map_comp := map_comp 𝒜

/-- The twisted-sections functor evaluates through the bundled object constructor. -/
@[simp]
theorem functor_obj (F : (Proj 𝒜).Modules) :
    (functor 𝒜).obj F = obj 𝒜 F := sorry

/-- The twisted-sections functor maps through the bundled graded-map constructor. -/
@[simp]
theorem functor_map {F G : (Proj 𝒜).Modules} (f : F ⟶ G) :
    (functor 𝒜).map f = map 𝒜 f := sorry

section Finite

variable [IsNoetherianRing A]

/-- 0BXF: Twisted sections of a coherent module form a finite `A`-module. -/
@[stacks 0BXF]
theorem finite (F : (Proj 𝒜).Modules) [hF : F.IsCoherent] :
    Module.Finite A (obj 𝒜 F) := sorry

/-- The finitely generated graded module of twisted sections of a coherent module. -/
@[stacks 0BXF]
noncomputable def fgObj (F : RingedSpace.Coh (Proj 𝒜).toRingedSpace) :
    GradedModule.Left.FG 𝒜 ℤ :=
  ⟨obj 𝒜 F.obj, finite 𝒜 F.obj (hF := F.property)⟩

/-- 0BXF: The twisted-sections functor lifted from coherent modules to finitely generated
graded modules. -/
@[stacks 0BXF]
noncomputable def fgFunctor :
    RingedSpace.Coh (Proj 𝒜).toRingedSpace ⥤ GradedModule.Left.FG 𝒜 ℤ :=
  (GradedModule.Left.isFG 𝒜 ℤ).lift
    ((SheafOfModules.isCoherent _).ι ⋙ functor 𝒜)
    (fun F ↦ finite 𝒜 F.obj (hF := F.property))

/-- The finite twisted-sections functor evaluates through `fgObj`. -/
@[simp]
theorem fgFunctor_obj (F : RingedSpace.Coh (Proj 𝒜).toRingedSpace) :
    (fgFunctor 𝒜).obj F = fgObj 𝒜 F := sorry

/-- The finite twisted-sections functor maps through the underlying graded map. -/
@[simp]
theorem fgFunctor_map {F G : RingedSpace.Coh (Proj 𝒜).toRingedSpace} (f : F ⟶ G) :
    ((fgFunctor 𝒜).map f).hom = map 𝒜 f.hom := sorry

end Finite

end Nonnegative

end NonnegativeBase

end AlgebraicGeometry.Proj.TwistedSections
