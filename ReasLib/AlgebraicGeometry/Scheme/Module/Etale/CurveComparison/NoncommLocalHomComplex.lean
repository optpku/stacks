/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHom
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace NoncommLocalHomComplex
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)
variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommLocalHom.modules h)]
variable (L : ChainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) ℕ)
variable (J : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℕ)

/-- The finite diagonal factor; L_i is placed in degree -i. -/
abbrev factor (n : ℕ) (i : Fin (n + 1)) :=
  NoncommLocalHom.obj h hc Y (L.X i.val) (J.X (n - i.val))

/-- Explicit finite product of local natural transformations, with pointwise restrictions. -/
def degreePresheaf (n : ℕ) : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Rᵐᵒᵖ where
  obj U := ModuleCat.of Rᵐᵒᵖ (∀ i : Fin (n + 1), (factor h hc Y L J n i).obj.obj U)
  map f := ModuleCat.ofHom
    { toFun := fun α i ↦ ((factor h hc Y L J n i).obj.map f).hom (α i)
      map_add' := by intros; ext i; exact map_add _ _ _
      map_smul' := by
        intro r α
        funext i
        exact ((factor h hc Y L J n i).obj.map f).hom.map_smul r (α i) }
  map_id := sorry
  map_comp := sorry

/-- Products of the already constructed sheaves glue componentwise. -/
theorem degree_isSheaf (n : ℕ) :
    Presheaf.IsSheaf Y.smallEtaleTopology (degreePresheaf h hc Y L J n) := sorry

/-- Degree n contains all n+1 factors, not a direct sum over an infinite diagonal. -/
def degree (n : ℕ) : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ) :=
  ⟨degreePresheaf h hc Y L J n, degree_isSheaf h hc Y L J n⟩

/-- Actual evaluation at a finite product coordinate. -/
def projection (n : ℕ) (i : Fin (n + 1)) :
    degree h hc Y L J n ⟶ factor h hc Y L J n i :=
  ObjectProperty.homMk
    { app := fun _ ↦ ModuleCat.ofHom
        { toFun := fun α ↦ α i
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      naturality := sorry }

/-- Actual finite product lift, coordinate by coordinate. -/
def lift {S : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)}
    (n : ℕ) (f : ∀ i : Fin (n + 1), S ⟶ factor h hc Y L J n i) :
    S ⟶ degree h hc Y L J n :=
  ObjectProperty.homMk
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun x i ↦ ((f i).hom.app U).hom x
          map_add' := by intros; ext i; exact map_add _ _ _
          map_smul' := by
            intro r x
            funext i
            exact ((f i).hom.app U).hom.map_smul r x }
      naturality := sorry }

/-- Postcomposition contributes only where the source coordinate exists. -/
def targetComponent (n : ℕ) (i : Fin (n + 2)) :
    degree h hc Y L J n ⟶ factor h hc Y L J (n + 1) i :=
  if hi : i.val ≤ n then
    projection h hc Y L J n ⟨i.val, by omega⟩ ≫
      NoncommLocalHom.postcomp h hc Y (J.d (n - i.val) (n + 1 - i.val))
  else 0

/-- The source coordinate shift uses a proved natural-number identity. -/
theorem sourceIndex (n i : ℕ) (hi : 0 < i) : n - (i - 1) = n + 1 - i := by omega

/-- Precomposition contributes only for i>0; it is literally zero at i=0. -/
def sourceComponent (n : ℕ) (i : Fin (n + 2)) :
    degree h hc Y L J n ⟶ factor h hc Y L J (n + 1) i :=
  if hi : 0 < i.val then
    projection h hc Y L J n ⟨i.val - 1, by omega⟩ ≫
      NoncommLocalHom.map h hc Y (L.d i.val (i.val - 1))
        (eqToHom (congrArg J.X (sourceIndex n i.val hi)))
  else 0

/-- Hom differential d_J φ - (-1)^n φ d_L, with both boundary cases explicit. -/
def component (n : ℕ) (i : Fin (n + 2)) :
    degree h hc Y L J n ⟶ factor h hc Y L J (n + 1) i :=
  targetComponent h hc Y L J n i +
    ((-1 : ℤ) ^ (n + 1)) • sourceComponent h hc Y L J n i

/-- The differential is the actual finite product lift of those components. -/
def differential (n : ℕ) : degree h hc Y L J n ⟶ degree h hc Y L J (n + 1) :=
  lift h hc Y L J (n + 1) (component h hc Y L J n)

/-- The two square-zero laws and cancellation of mixed terms imply d²=0. -/
theorem differential_sq (n : ℕ) :
    differential h hc Y L J n ≫ differential h hc Y L J (n + 1) = 0 := sorry

/-- The nonnegative internal-Hom cochain complex, with no resolution assertion. -/
def complex : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)) ℕ :=
  CochainComplex.of (degree h hc Y L J) (differential h hc Y L J)
    (differential_sq h hc Y L J)

/-- Actual extension by zero to integral degrees. -/
def integerComplex : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)) ℤ :=
  (complex h hc Y L J).extend ComplexShape.embeddingUpNat

/-- A source in degrees 2-i gives this canonical even shift of the Hom complex. -/
def shiftedComplex : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)) ℤ :=
  (integerComplex h hc Y L J)⟦(2 : ℤ)⟧

/-- The missing source contribution at i=0 is zero by construction. -/
theorem sourceComponent_zero (n : ℕ) :
    sourceComponent h hc Y L J n ⟨0, by omega⟩ = 0 := by
  simp [sourceComponent]

/-- The missing target contribution at i=n+1 is zero by construction. -/
theorem targetComponent_last (n : ℕ) :
    targetComponent h hc Y L J n ⟨n + 1, by omega⟩ = 0 := by
  simp [targetComponent]

end NoncommLocalHomComplex
