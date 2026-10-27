/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Triangulated
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.Biproduct
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Comparison
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.Category
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Shift.GradedHom
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Triangulated

/-!
# Triangulated tensoring over an algebra sheaf

Tensoring with a fixed complex over its endomorphism DGA commutes with shifts before passage to
derived categories.  This file owns the explicit shift maps and their homotopy-category
compatibility for an arbitrary commutative coefficient ring.
-/

@[expose] public section

noncomputable section

universe r u v w z

open CategoryTheory
open CochainComplex.HomComplex
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule SheafOfModules.CommAlg

namespace SheafOfModules.CommAlg.TensorWithObject

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ (CommAlgCat.{w} R) CommRingCat.{w})]
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, max u z}]
variable [HasWeakSheafify J AddCommGrpCat.{max u z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u z}]
variable {O : Sheaf J (CommAlgCat.{w} R)}

/-- The standard homotopy category of complexes of module sheaves over `O`. -/
@[stacks 09LW "homotopy category of modules over an algebra sheaf"]
abbrev TargetHomotopy :=
  HomotopyCategory
    (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)
    (ComplexShape.up ℤ)

/-- A closed homogeneous DG-module map remains a cocycle after tensoring with `K`. -/
@[stacks 09LW "tensoring closed maps over a coefficient ring gives cocycles"]
def mapCocycle (K : Complex.{r, u, v, w, max u z} O)
    {M N : Modules K} {k : ℤ}
    (f : DifferentialGradedModule.ClosedGradedHom (endDGA K) M N k) :
    Cocycle (obj K M) (obj K N) k :=
  Cocycle.mk (map K f.1) (k + 1) rfl sorry

/-- The canonical tensor-shift map is the unsigned reindexing `m ⊗ x ↦ m ⊗ x`.
For `m` of degree `p` and `x` of degree `q`, its source degree is `p + q - k` and
its target tensor degrees are `p - k` and `q`.  The shifted differentials agree since
`(-1)^(p - k) = (-1)^(p + k)`.  We assemble the components directly: the generic
`Cocycle.equivHomShift'` introduces the extraneous factor `(-1)^(k*(k-1)/2)`. -/
@[stacks 09LW "tensor-shift map over a coefficient ring"]
def shiftHom (K : Complex.{r, u, v, w, max u z} O) (M : Modules K) (k : ℤ) :
    (obj K M)⟦k⟧ ⟶ obj K (M[k]) where
  f n := ((obj K M).shiftFunctorObjXIso k n (n + k) rfl).hom ≫
    (map K (DifferentialGradedModule.Shift.toGradedHom M k).1).v
      (n + k) n (by omega)
  comm' := sorry

/-- The forward tensor-shift map has unsigned components, before taking homotopy or homology. -/
@[simp]
theorem shiftHom_f (K : Complex.{r, u, v, w, max u z} O) (M : Modules K) (k n : ℤ) :
    (shiftHom K M k).f n =
      ((obj K M).shiftFunctorObjXIso k n (n + k) rfl).hom ≫
        (map K (DifferentialGradedModule.Shift.toGradedHom M k).1).v
          (n + k) n (by omega) := rfl

/-- Tensoring the reverse homogeneous identity gives the inverse shift map. -/
@[stacks 09LW "inverse tensor-shift map over a coefficient ring"]
def shiftInv (K : Complex.{r, u, v, w, max u z} O) (M : Modules K) (k : ℤ) :
    obj K (M[k]) ⟶ (obj K M)⟦k⟧ :=
  Cocycle.equivHomShift.symm
    (mapCocycle K (DifferentialGradedModule.Shift.fromGradedHom M k))

/-- Tensoring with `K` commutes with the explicit shift of a right DG module. -/
@[stacks 09LW "tensor-shift isomorphism over a coefficient ring"]
def shiftIso (K : Complex.{r, u, v, w, max u z} O) (M : Modules K) (k : ℤ) :
    (obj K M)⟦k⟧ ≅ obj K (M[k]) where
  hom := shiftHom K M k
  inv := shiftInv K M k
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Lemma 22.35.2 (09LW): tensoring with `K` on enriched homotopy categories. -/
@[stacks 09LW "tensor functor on algebra-sheaf homotopy categories"]
def homotopyFunctor (K : Complex.{r, u, v, w, max u z} O) :
    DifferentialGradedCategory.K R (Modules K) ⥤
      TargetHomotopy.{r, u, v, w, z} (R := R) (J := J) (O := O) :=
  (tensorFunctor K).mapK ⋙
    (CategoryTheory.CochainComplex.Enriched.Over.toMathlib
      (R := R)
      (C := SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O))

/-- The module-sheaf homotopy category carries the coefficient-ring linear structure. -/
@[stacks 09LW "linearity of the module-sheaf homotopy category"]
noncomputable instance targetHomotopy_linear :
    Linear R (TargetHomotopy.{r, u, v, w, z} (R := R) (J := J) (O := O)) := inferInstance

/-- Tensoring with `K` is linear on the enriched homotopy category. -/
@[stacks 09LW "linearity of the tensor homotopy functor"]
noncomputable instance homotopyFunctor_linear
    (K : Complex.{r, u, v, w, max u z} O) : (homotopyFunctor K).Linear R := sorry

/-- The objectwise shift comparison for the tensor homotopy functor. -/
@[stacks 09LW "objectwise tensor-shift comparison over a coefficient ring"]
def homotopyShiftIsoApp (K : Complex.{r, u, v, w, max u z} O)
    (M : DifferentialGradedCategory.K R (Modules K)) (k : ℤ) :
    ((DifferentialGradedModule.Shift.K.functor (endDGA K) k ⋙
        homotopyFunctor K).obj M) ≅
      ((homotopyFunctor K ⋙
        shiftFunctor
          (TargetHomotopy.{r, u, v, w, z} (R := R) (J := J) (O := O)) k).obj M) :=
  (HomotopyCategory.quotient
      (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)
      (ComplexShape.up ℤ)).mapIso (shiftIso K M.obj k).symm ≪≫
    ((HomotopyCategory.quotient
      (SheafOfModules.CommAlg.Modules.{r, u, v, w, max u z} O)
      (ComplexShape.up ℤ)).commShiftIso k).app (obj K M.obj)

/-- The objectwise tensor-shift comparison is natural in the homotopy object. -/
@[reassoc, stacks 09LW "naturality of the tensor-shift comparison over a coefficient ring"]
theorem homotopyShiftIso_naturality
    (K : Complex.{r, u, v, w, max u z} O) (k : ℤ)
    {M N : DifferentialGradedCategory.K R (Modules K)} (f : M ⟶ N) :
    (DifferentialGradedModule.Shift.K.functor (endDGA K) k ⋙
        homotopyFunctor K).map f ≫ (homotopyShiftIsoApp K N k).hom =
      (homotopyShiftIsoApp K M k).hom ≫
        (homotopyFunctor K ⋙
          shiftFunctor
            (TargetHomotopy.{r, u, v, w, z} (R := R) (J := J) (O := O)) k).map f := sorry

/-- Tensoring with `K` commutes naturally with the explicit source and target shifts. -/
@[stacks 09LW "natural tensor-shift comparison over a coefficient ring"]
def homotopyShiftIso (K : Complex.{r, u, v, w, max u z} O) (k : ℤ) :
    DifferentialGradedModule.Shift.K.functor (endDGA K) k ⋙ homotopyFunctor K ≅
      homotopyFunctor K ⋙
        shiftFunctor
          (TargetHomotopy.{r, u, v, w, z} (R := R) (J := J) (O := O)) k :=
  NatIso.ofComponents (fun M ↦ homotopyShiftIsoApp K M k)
    (fun f ↦ homotopyShiftIso_naturality K k f)

/-- Tensoring with `K` commutes with the canonical abstract shifts on homotopy categories. -/
@[stacks 09LW "canonical tensor-shift comparison over a coefficient ring"]
def homotopyCommShiftIso (K : Complex.{r, u, v, w, max u z} O) (k : ℤ) :
    shiftFunctor (DifferentialGradedCategory.K R (Modules K)) k ⋙ homotopyFunctor K ≅
      homotopyFunctor K ⋙
        shiftFunctor
          (TargetHomotopy.{r, u, v, w, z} (R := R) (J := J) (O := O)) k :=
  (Functor.isoWhiskerRight
      (eqToIso (DifferentialGradedModule.Shift.K.shiftFunctor_eq (endDGA K) k))
      (homotopyFunctor K)).trans (homotopyShiftIso K k)

/-- The tensor shift comparison agrees with the canonical zero-shift comparison. -/
@[stacks 09LW "zero coherence for tensor shifts over a coefficient ring"]
theorem homotopyCommShiftIso_zero (K : Complex.{r, u, v, w, max u z} O) :
    homotopyCommShiftIso K 0 = Functor.CommShift.isoZero (homotopyFunctor K) ℤ := sorry

/-- The tensor shift comparison is coherent with addition of shifts. -/
@[stacks 09LW "additive coherence for tensor shifts over a coefficient ring"]
theorem homotopyCommShiftIso_add (K : Complex.{r, u, v, w, max u z} O)
    (i j : ℤ) :
    homotopyCommShiftIso K (i + j) =
      Functor.CommShift.isoAdd
      (homotopyCommShiftIso K i) (homotopyCommShiftIso K j) := sorry

/-- The tensor homotopy functor has canonical compatibility with integer shifts. -/
@[stacks 09LW "homotopy tensor over a coefficient ring commutes with shifts"]
noncomputable instance homotopyFunctor_commShift
    (K : Complex.{r, u, v, w, max u z} O) : (homotopyFunctor K).CommShift ℤ where
  commShiftIso := homotopyCommShiftIso K
  commShiftIso_zero := homotopyCommShiftIso_zero K
  commShiftIso_add := homotopyCommShiftIso_add K

/-- Tensoring with `K` is triangulated on the homotopy categories. -/
@[stacks 09LW "tensor over a coefficient ring is exact on homotopy categories"]
instance homotopyFunctor_isTriangulated
    (K : Complex.{r, u, v, w, max u z} O) : (homotopyFunctor K).IsTriangulated := sorry

end SheafOfModules.CommAlg.TensorWithObject
