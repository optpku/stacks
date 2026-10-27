/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealQuotient
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Pullback.Kernel
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.SupportedQuotient.Factorization
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Factorization through an ideal quotient

Kernel containment, equivalently vanishing of the pulled-back ideal, characterizes the unique
factorization through an ideal quotient. The sheaf map and locally ringed-space morphism are
explicit data obtained from the generic ideal-sheaf quotient eliminator and the supported-quotient
lift; the factorization and uniqueness laws remain separate proof obligations.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.IdealQuotient

variable {X Y : LocallyRingedSpace.{u}}

/-- The quotient-sheaf map induced by kernel containment. -/
@[stacks 01HP "sheaf map induced by ideal-kernel containment"]
noncomputable def sheafLift
    (I : IdealSubobject X) (f : Y ⟶ X)
    (hI : I ≤ Hom.kernelIdealSubobject f) :
    sheaf I ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj Y.𝒪 :=
  IdealSheaf.Quotient.lift I (Hom.commRingSheafPushforwardMap f) hI

/-- The quotient projection followed by the induced sheaf map is the structure-sheaf map of the
ambient morphism. -/
@[reassoc, simp, stacks 01HP "ideal quotient sheaf-lift computation"]
theorem projection_comp_sheafLift
    (I : IdealSubobject X) (f : Y ⟶ X)
    (hI : I ≤ Hom.kernelIdealSubobject f) :
    projection I ≫ sheafLift I f hI =
      Hom.commRingSheafPushforwardMap f := by
  apply Sheaf.hom_ext
  change (IdealSheaf.Quotient.presheafProjection.{u, u, u} I ≫
      toSheafify _ (IdealSheaf.Quotient.presheaf.{u, u, u} I)) ≫
      sheafifyLift _ (IdealSheaf.Quotient.presheafLift.{u, u, u} I
        (Hom.commRingSheafPushforwardMap f) hI) _ = f.c
  rw [Category.assoc, toSheafify_sheafifyLift]
  ext U s
  rfl

/-- The canonical morphism to the ideal quotient induced by kernel containment. -/
@[stacks 01HP "canonical ideal quotient lift"]
noncomputable def lift
    (I : IdealSubobject X) (f : Y ⟶ X)
    (hI : I ≤ Hom.kernelIdealSubobject f) :
    Y ⟶ space I :=
  SupportedQuotient.lift (presentation I) f (sheafLift I f hI)
    (projection_comp_sheafLift I f hI)

/-- The canonical ideal quotient lift factors the original morphism. -/
@[reassoc, simp, stacks 01HP "ideal quotient lift computation"]
theorem lift_comp_ι
    (I : IdealSubobject X) (f : Y ⟶ X)
    (hI : I ≤ Hom.kernelIdealSubobject f) :
    lift I f hI ≫ ι I = f := by
  exact SupportedQuotient.lift_comp_ι (presentation I) f (sheafLift I f hI)
    (projection_comp_sheafLift I f hI)

/-- The canonical ideal quotient lift is the unique morphism over the ambient locally ringed
space. -/
@[stacks 01HP "ideal quotient lift uniqueness"]
theorem lift_unique
    (I : IdealSubobject X) (f : Y ⟶ X)
    (hI : I ≤ Hom.kernelIdealSubobject f)
    (g : Y ⟶ space I) (hg : g ≫ ι I = f) :
    g = lift I f hI := by
  exact SupportedQuotient.lift_unique (presentation I) f (sheafLift I f hI)
    (projection_comp_sheafLift I f hI) g hg

private theorem le_kernel_comp_ι (I : IdealSubobject X) (g : Y ⟶ space I) :
    I ≤ Hom.kernelIdealSubobject (g ≫ ι I) := by
  apply Limits.le_kernelSubobject _ I
  ext U s
  change g.c.app _ ((SupportedQuotient.pushforwardComparison (presentation I)).hom.app U
    ((projection I).hom.app U (SheafOfModules.Subobject.inclusionApp I U s))) = 0
  let x : X.𝒪.obj.obj U := SheafOfModules.Subobject.inclusionApp I U s
  have hx : x ∈ IdealSheaf.sections.{u, u, u} I U := ⟨s, rfl⟩
  have hquot : Ideal.Quotient.mk (IdealSheaf.sections.{u, u, u} I U) x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hx
  have hzero : (projection I).hom.app U x = 0 := by
    change (toSheafify _ (IdealSheaf.Quotient.presheaf.{u, u, u} I)).app U
      (Ideal.Quotient.mk _ x) = 0
    exact (congrArg ((toSheafify _ (IdealSheaf.Quotient.presheaf.{u, u, u} I)).app U)
      hquot).trans ((toSheafify _ (IdealSheaf.Quotient.presheaf.{u, u, u} I)).app U).hom.map_zero
  rw [hzero]
  exact (congrArg (g.c.app _)
    ((SupportedQuotient.pushforwardComparison (presentation I)).hom.app U).hom.map_zero).trans
      (g.c.app _).hom.map_zero

/-- Two morphisms into an ideal quotient are equal when they agree after composition with the
canonical inclusion into the ambient locally ringed space. -/
@[stacks 01HP "ideal quotient extensionality"]
theorem hom_ext (I : IdealSubobject X) {g h : Y ⟶ space I}
    (w : g ≫ ι I = h ≫ ι I) :
    g = h := by
  have hI := le_kernel_comp_ι I g
  calc
    g = lift I (g ≫ ι I) hI := lift_unique I _ hI g rfl
    _ = h := (lift_unique I _ hI h w.symm).symm

/-- The canonical inclusion of an ideal quotient into its ambient locally ringed space is a
monomorphism. -/
@[stacks 01HP "ideal quotient inclusion is monic"]
instance ι_mono (I : IdealSubobject X) : Mono (ι I) where
  right_cancellation _ _ w := hom_ext I w

/-- The canonical ideal quotient lift induced by vanishing of the pulled-back ideal map. -/
@[stacks 01HP "canonical ideal quotient lift from vanishing"]
noncomputable def liftOfVanishing
    (I : IdealSubobject X) (f : Y ⟶ X)
    (hzero : I.pullbackMap f = 0) :
    Y ⟶ space I :=
  lift I f ((IdealSubobject.pullback_eq_zero_iff_le_kernel I f).mp hzero)

/-- The ideal quotient lift induced by vanishing factors the original morphism. -/
@[reassoc, simp, stacks 01HP "vanishing-induced ideal quotient lift computation"]
theorem liftOfVanishing_comp_ι
    (I : IdealSubobject X) (f : Y ⟶ X)
    (hzero : I.pullbackMap f = 0) :
    liftOfVanishing I f hzero ≫ ι I = f := by
  exact lift_comp_ι I f ((IdealSubobject.pullback_eq_zero_iff_le_kernel I f).mp hzero)

/-- Kernel containment induces a unique morphism to the ideal quotient over the ambient locally
ringed space. -/
@[stacks 01HP "ideal quotient universal property"]
theorem existsUnique_lift
    (I : IdealSubobject X) (f : Y ⟶ X)
    (hI : I ≤ Hom.kernelIdealSubobject f) :
    ∃! g : Y ⟶ space I, g ≫ ι I = f := by
  exact ⟨lift I f hI, lift_comp_ι I f hI, fun g hg => lift_unique I f hI g hg⟩

/-- A morphism factors through the ideal quotient exactly when its kernel contains the defining
ideal. -/
@[stacks 01HP "ideal quotient factorization criterion"]
theorem exists_lift_iff_le_kernel
    (I : IdealSubobject X) (f : Y ⟶ X) :
    (∃ g : Y ⟶ space I, g ≫ ι I = f) ↔
      I ≤ Hom.kernelIdealSubobject f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact le_kernel_comp_ι I g
  · intro hI
    exact (existsUnique_lift I f hI).exists

/-- A morphism has a unique factorization through an ideal quotient exactly when its kernel
contains the defining ideal. -/
@[stacks 01HP "unique ideal quotient factorization criterion"]
theorem existsUnique_lift_iff_le_kernel
    (I : IdealSubobject X) (f : Y ⟶ X) :
    (∃! g : Y ⟶ space I, g ≫ ι I = f) ↔
      I ≤ Hom.kernelIdealSubobject f := by
  constructor
  · intro h
    exact (exists_lift_iff_le_kernel I f).mp h.exists
  · intro hI
    exact existsUnique_lift I f hI

/-- Vanishing of the pulled-back ideal induces a unique morphism to the ideal quotient. -/
@[stacks 01HP "ideal quotient factorization from vanishing"]
theorem existsUnique_lift_of_vanishing
    (I : IdealSubobject X) (f : Y ⟶ X)
    (hzero : I.pullbackMap f = 0) :
    ∃! g : Y ⟶ space I, g ≫ ι I = f := by
  exact existsUnique_lift I f ((IdealSubobject.pullback_eq_zero_iff_le_kernel I f).mp hzero)

end AlgebraicGeometry.LocallyRingedSpace.IdealQuotient
