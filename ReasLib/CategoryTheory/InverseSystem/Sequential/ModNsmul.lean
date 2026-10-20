module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.InverseSystem.Sequential.EventuallyConstant

/-!
# Nsmul reductions of sequential inverse systems

The reduction maps are induced by scalar multiplication and cokernel projections.
Eventual constancy retains an exponent-dependent stabilization bound.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Sheaf

noncomputable section

universe u v

namespace CategoryTheory.Limits

/-- The cokernel of multiplication by `n` on an object of a preadditive category. -/
abbrev nsmulCokernel {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
    (X : C) (n : ℕ) : C :=
  cokernel (n • 𝟙 X)

/-- `nsmulCokernel` is the cokernel of `n • 𝟙`. -/
theorem nsmulCokernel_eq {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
    (X : C) (n : ℕ) :
    nsmulCokernel X n = cokernel (n • 𝟙 X) := sorry

/-- The map of nsmul cokernels induced by a morphism of objects. -/
def nsmulCokernelMap {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
    {X Y : C} (n : ℕ) (f : X ⟶ Y) :
    nsmulCokernel X n ⟶ nsmulCokernel Y n :=
  cokernel.map (n • 𝟙 X) (n • 𝟙 Y) f f
    ((nsmul_comp (𝟙 X) f n).trans
      ((congrArg (fun h => n • h) ((Category.id_comp f).trans (Category.comp_id f).symm)).trans
        (comp_nsmul f (𝟙 Y) n).symm))

/-- `nsmulCokernelMap` intertwines the cokernel projections. -/
theorem nsmulCokernelMap_π {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
    {X Y : C} (n : ℕ) (f : X ⟶ Y) :
    cokernel.π (n • 𝟙 X) ≫ nsmulCokernelMap n f = f ≫ cokernel.π (n • 𝟙 Y) := sorry

/-- The canonical reduction `coker ((b * m) • 𝟙 X) ⟶ coker (b • 𝟙 X)` along `m • 𝟙 X`. -/
def nsmulCokernelReduce {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
    (X : C) (m b : ℕ) :
    nsmulCokernel X (b * m) ⟶ nsmulCokernel X b :=
  cokernel.map ((b * m) • 𝟙 X) (b • 𝟙 X) (m • 𝟙 X) (𝟙 X)
    ((Category.comp_id ((b * m) • 𝟙 X)).trans
      ((mul_nsmul (𝟙 X) b m).trans
        ((congrArg (fun h => m • h) (Category.id_comp (b • 𝟙 X)).symm).trans
          (nsmul_comp (𝟙 X) (b • 𝟙 X) m).symm)))

/-- `nsmulCokernelReduce` identifies the two cokernel projections. -/
theorem nsmulCokernelReduce_π {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]
    (X : C) (m b : ℕ) :
    cokernel.π ((b * m) • 𝟙 X) ≫ nsmulCokernelReduce X m b =
      cokernel.π (b • 𝟙 X) := sorry

end CategoryTheory.Limits

namespace CategoryTheory.SequentialInverseSystem

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCokernels C]

/-- The object `G_n / ℓ^{k+1} G_n` at a 0-based stage. -/
def modNsmulFamily (G : SequentialInverseSystem C) (ℓ k n : ℕ) : C :=
  nsmulCokernel (G.family n) (ℓ ^ (k + 1))

/-- The successor map `G_{n+1} / ℓ^{k+1} G_{n+1} ⟶ G_n / ℓ^{k+1} G_n`. -/
def modNsmulStepMap (G : SequentialInverseSystem C) (ℓ k n : ℕ) :
    modNsmulFamily G ℓ k (n + 1) ⟶ modNsmulFamily G ℓ k n :=
  nsmulCokernelMap (ℓ ^ (k + 1)) (G.stepMap n)

/-- The inverse system of nsmul cokernels `G_n / ℓ^{k+1} G_n`. -/
def modNsmulSystem (G : SequentialInverseSystem C) (ℓ k : ℕ) :
    SequentialInverseSystem C :=
  Functor.ofOpSequence (modNsmulStepMap G ℓ k)

/-- Stage `n` of the reduced system is the nsmul cokernel of the original stage. -/
theorem modNsmulSystem_obj (G : SequentialInverseSystem C) (ℓ k n : ℕ) :
    (G.modNsmulSystem ℓ k).family n = modNsmulFamily G ℓ k n := sorry

/-- Successor maps of the reduced system are the named nsmul cokernel maps. -/
theorem modNsmulSystem_stepMap (G : SequentialInverseSystem C) (ℓ k n : ℕ) :
    (G.modNsmulSystem ℓ k).stepMap n = modNsmulStepMap G ℓ k n := sorry

/-- The source-indexed reduction `G_n / ℓ^k G_n`. -/
abbrev modNsmulComponent (G : SequentialInverseSystem C) (ℓ : ℕ) (k n : ℕ+) : C :=
  (G.modNsmulSystem ℓ k.natPred).family n.natPred

/-- The source component `G_n / ℓ^k G_n` is the nsmul cokernel at 0-based stages `n-1`. -/
theorem modNsmulComponent_eq (G : SequentialInverseSystem C) (ℓ : ℕ) (k n : ℕ+) :
    modNsmulComponent G ℓ k n = modNsmulFamily G ℓ k.natPred n.natPred := sorry

/-- The displayed successor `G_{n+1} / ℓ^k G_{n+1} ⟶ G_n / ℓ^k G_n`. -/
theorem modNsmulComponent_stepMap (G : SequentialInverseSystem C) (ℓ : ℕ) (k n : ℕ+) :
    (G.modNsmulSystem ℓ k.natPred).stepMap n.natPred =
      modNsmulStepMap G ℓ k.natPred n.natPred := sorry

/-- The pointwise reduction `G_n / ℓ^{k+2} G_n ⟶ G_n / ℓ^{k+1} G_n`. -/
def modNsmulReduceApp (G : SequentialInverseSystem C) (ℓ k n : ℕ) :
    modNsmulFamily G ℓ (k + 1) n ⟶ modNsmulFamily G ℓ k n :=
  nsmulCokernelReduce (G.family n) ℓ (ℓ ^ (k + 1))

/-- The reduction natural transformation `G / ℓ^{k+2} G ⟶ G / ℓ^{k+1} G`. -/
def modNsmulReduce (G : SequentialInverseSystem C) (ℓ k : ℕ) :
    G.modNsmulSystem ℓ (k + 1) ⟶ G.modNsmulSystem ℓ k :=
  NatTrans.ofOpSequence (modNsmulReduceApp G ℓ k) (fun _ ↦ sorry)

/-- Components of `modNsmulReduce` are the pointwise nsmul cokernel reductions. -/
theorem modNsmulReduce_app (G : SequentialInverseSystem C) (ℓ k n : ℕ) :
    (G.modNsmulReduce ℓ k).app (op n) = modNsmulReduceApp G ℓ k n := sorry

/-- Eventual constancy of every reduced system `G / ℓ^{k+1} G`. -/
def IsEventuallyConstantModNsmul (G : SequentialInverseSystem C) (ℓ : ℕ) : Prop :=
  ∀ k, ∃ N, (G.modNsmulSystem ℓ k).IsEventuallyConstantTo (op N)

/-- Eventual constancy of reductions is invertibility of late reduced successor maps. -/
theorem isEventuallyConstantModNsmul_iff (G : SequentialInverseSystem C) (ℓ : ℕ) :
    G.IsEventuallyConstantModNsmul ℓ ↔
      ∀ k, ∃ N, ∀ n, N ≤ n → IsIso ((G.modNsmulSystem ℓ k).stepMap n) := sorry

end CategoryTheory.SequentialInverseSystem
