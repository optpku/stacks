/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.InverseSystem.HomOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived cross-index morphisms of ordinary left module systems

An ordinary left DG-module system has a canonical derived object at every stage.  A
cross-index morphism is a map from a later derived stage to the restriction of an earlier
derived stage along the corresponding opposite DGA transition.
-/

@[expose] public section

noncomputable section

universe u x v

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem.LeftSystem.Derived

variable {R : Type u} [CommRing R]

/-- The derived stage of an ordinary left DG-module inverse system. -/
@[stacks 0GZI "derived stages of ordinary left DG-module systems"]
abbrev stage
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) (n : ℕ) :=
  (DifferentialGradedModule.InverseSystem.Derived.Left.stageSource A n).obj N

/-- A derived morphism from stage `j` of `N` to the restriction of stage `i` of `N'`, for
`i ≤ j`. -/
@[stacks 0GZI "cross-index derived morphisms of ordinary left DG-module systems"]
abbrev HomOver
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N N' : LeftSystem.{u, x, v} A) {i j : ℕ} (hij : i ≤ j) :=
  stage A N j ⟶
    (DifferentialGradedModule.InverseSystem.Derived.Left.restriction A hij).obj
      (stage A N' i)

namespace HomOver

/-- The identity derived cross-index morphism over a reflexive inequality. -/
noncomputable def id
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) (i : ℕ) :
    HomOver A N N (le_refl i) :=
  (DifferentialGradedModule.InverseSystem.Derived.Left.restrictionReflIso A i).hom.app
    (stage A N i)

/-- The canonical derived cross-index morphism induced by an ordinary left-system
transition. -/
@[stacks 0GZI "derived transition of an ordinary left DG-module system"]
noncomputable def transition
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) {i j : ℕ} (hij : i ≤ j) :
    HomOver A N N hij :=
  DifferentialGradedModule.InverseSystem.Derived.Restriction.sourceApp
    (A ⋙ CochainDGAlgebra.oppositeFunctor R) hij N

/-- Composition of consecutive derived cross-index morphisms, using the canonical
composition comparison for derived restriction. -/
noncomputable def comp
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {L M N : LeftSystem.{u, x, v} A} {i j k : ℕ}
    {hij : i ≤ j} {hjk : j ≤ k}
    (f : HomOver A L M hjk) (g : HomOver A M N hij) :
    HomOver A L N (Nat.le_trans hij hjk) :=
  f ≫
    (DifferentialGradedModule.InverseSystem.Derived.Left.restriction A hjk).map g ≫
    (DifferentialGradedModule.InverseSystem.Derived.Left.restrictionCompIso
      A hij hjk).hom.app (stage A N i)

/-- Composing with the identity at the target stage leaves a derived cross-index morphism
unchanged. -/
@[simp]
theorem comp_id
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {L M : LeftSystem.{u, x, v} A} {i j : ℕ} {hij : i ≤ j}
    (f : HomOver A L M hij) :
    comp f (id A M i) = f := sorry

/-- Composing with the identity at the source stage leaves a derived cross-index morphism
unchanged. -/
@[simp]
theorem id_comp
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {L M : LeftSystem.{u, x, v} A} {i j : ℕ} {hij : i ≤ j}
    (f : HomOver A L M hij) :
    comp (id A L j) f = f := sorry

/-- Composition of three consecutive derived cross-index morphisms is associative. -/
theorem comp_assoc
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {K L M N : LeftSystem.{u, x, v} A} {i j k l : ℕ}
    {hij : i ≤ j} {hjk : j ≤ k} {hkl : k ≤ l}
    (f : HomOver A K L hkl) (g : HomOver A L M hjk)
    (h : HomOver A M N hij) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- The canonical derived transition over a reflexive inequality is the identity
cross-index morphism. -/
@[simp]
theorem transition_refl
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) (i : ℕ) :
    transition A N (le_refl i) = id A N i := sorry

/-- The canonical derived transition through an intermediate stage is the composite of the
two canonical derived transitions. -/
theorem transition_comp
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    transition A N (Nat.le_trans hij hjk) =
      comp (transition A N hjk) (transition A N hij) := sorry

/-- Send a source-shaped cross-index morphism through the global localization, using the
canonical factorization isomorphisms at its source and target stages. -/
@[stacks 0GZI "localization of cross-index morphisms of left module systems"]
noncomputable def toGlobal
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {N N' : LeftSystem.{u, x, v} A} {i j : ℕ} {hij : i ≤ j}
    (f : HomOver A N N' hij) :
    DifferentialGradedModule.InverseSystem.Derived.Left.HomOver A
      ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N)
      ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N') hij :=
  (DifferentialGradedModule.InverseSystem.Derived.Left.evalFactors A j).hom.app N ≫
    f ≫
      (DifferentialGradedModule.InverseSystem.Derived.Left.restriction A hij).map
        ((DifferentialGradedModule.InverseSystem.Derived.Left.evalFactors A i).inv.app N')

private theorem iso_conjugate_identity
    {C : Type*} [Category* C] (F : C ⥤ C) (ε : 𝟭 C ≅ F)
    {X Y : C} (e : X ≅ Y) :
    e.hom ≫ ε.hom.app Y ≫ F.map e.inv = ε.hom.app X := by
  change (𝟭 C).map e.hom ≫ ε.hom.app Y ≫ F.map e.inv = ε.hom.app X
  rw [← Category.assoc]
  rw [ε.hom.naturality]
  rw [Category.assoc, ← F.map_comp, e.hom_inv_id, F.map_id, Category.comp_id]

private theorem iso_conjugate_composition
    {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂) (α : F ⋙ G ≅ H)
    {X₀ Y₀ : C₀} {X₁ Y₁ : C₁} {X₂ Y₂ : C₂}
    (e₀ : X₀ ≅ Y₀) (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂)
    (f : Y₂ ⟶ G.obj Y₁) (g : Y₁ ⟶ F.obj Y₀) :
    e₂.hom ≫ (f ≫ G.map g ≫ α.hom.app Y₀) ≫ H.map e₀.inv =
      (e₂.hom ≫ f ≫ G.map e₁.inv) ≫
        G.map (e₁.hom ≫ g ≫ F.map e₀.inv) ≫ α.hom.app X₀ := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc, e₁.inv_hom_id, G.map_id, Category.id_comp]
  exact congrArg (fun t ↦ e₂.hom ≫ f ≫ G.map g ≫ t) (α.hom.naturality e₀.inv).symm

/-- Localization carries an identity source-shaped cross-index morphism to the global
identity cross-index morphism. -/
@[simp]
theorem toGlobal_id
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) (i : ℕ) :
    toGlobal (id A N i) =
      DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.id A
        ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N) i := by
  exact iso_conjugate_identity
    (DifferentialGradedModule.InverseSystem.Derived.Left.restriction A (le_refl i))
    (DifferentialGradedModule.InverseSystem.Derived.Left.restrictionReflIso A i)
    ((DifferentialGradedModule.InverseSystem.Derived.Left.evalFactors A i).app N)

/-- Localization carries the source-shaped transition to the canonical global transition. -/
@[simp]
theorem toGlobal_transition
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (N : LeftSystem.{u, x, v} A) {i j : ℕ} (hij : i ≤ j) :
    toGlobal (transition A N hij) =
      DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.transition A
        ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N) hij := by
  let B := A ⋙ CochainDGAlgebra.oppositeFunctor R
  exact (Localization.liftNatTrans_app
    (DifferentialGradedModule.InverseSystem.Derived.Q B) (quasiIso B)
    (DifferentialGradedModule.InverseSystem.Derived.stageSource B j)
    (DifferentialGradedModule.InverseSystem.Derived.stageSource B i ⋙
      CochainDGAlgebra.Hom.Derived.restriction
        (CategoryTheory.SequentialInverseSystem.transitionMap B hij))
    (DifferentialGradedModule.InverseSystem.Derived.eval B j)
    (DifferentialGradedModule.InverseSystem.Derived.eval B i ⋙
      CochainDGAlgebra.Hom.Derived.restriction
        (CategoryTheory.SequentialInverseSystem.transitionMap B hij))
    (DifferentialGradedModule.InverseSystem.Derived.Restriction.source B hij) N).symm

/-- Localization preserves composition of source-shaped cross-index morphisms. -/
theorem toGlobal_comp
    {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}
    {L M N : LeftSystem.{u, x, v} A} {i j k : ℕ}
    {hij : i ≤ j} {hjk : j ≤ k}
    (f : HomOver A L M hjk) (g : HomOver A M N hij) :
    toGlobal (comp f g) =
      DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.comp
        (toGlobal f) (toGlobal g) := by
  exact iso_conjugate_composition
    (DifferentialGradedModule.InverseSystem.Derived.Left.restriction A hij)
    (DifferentialGradedModule.InverseSystem.Derived.Left.restriction A hjk)
    (DifferentialGradedModule.InverseSystem.Derived.Left.restriction A (Nat.le_trans hij hjk))
    (DifferentialGradedModule.InverseSystem.Derived.Left.restrictionCompIso A hij hjk)
    ((DifferentialGradedModule.InverseSystem.Derived.Left.evalFactors A i).app N)
    ((DifferentialGradedModule.InverseSystem.Derived.Left.evalFactors A j).app M)
    ((DifferentialGradedModule.InverseSystem.Derived.Left.evalFactors A k).app L) f g

end HomOver

end DifferentialGradedModule.InverseSystem.LeftSystem.Derived
