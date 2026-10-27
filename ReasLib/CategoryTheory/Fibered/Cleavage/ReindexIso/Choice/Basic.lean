/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso.Composition
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparing reindexing for different cleavages

Any two strongly cartesian lifts of the same base arrow and codomain have canonically isomorphic
domains. This leaf packages that uniqueness comparison in the standard fiber, proves its
factorization and naturality interfaces, and assembles it into a natural isomorphism between the
two reindexing functors.
-/

@[expose] public section

universe vC vS uC uS

namespace CategoryTheory

open Functor

variable {C : Type uC} [Category.{vC} C]
variable {S : Type uS} [Category.{vS} S]

namespace Functor.Cleavage

variable {p : S ⥤ C}

/-- The ambient canonical isomorphism between the reindexing objects selected by two cleavages.
It is the domain comparison between their strongly cartesian arrows over the same base arrow. -/
noncomputable def Reindex.uniqueAmbientIso
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (chi₁.reindexObj f x).1 ≅ (chi₂.reindexObj f x).1 :=
  IsStronglyCartesian.DomainIso.ofBaseIso (g := Iso.refl V) p
    (Category.id_comp f).symm
    (chi₂.cartesianHom f x) (chi₁.cartesianHom f x)
    (chi₂.reindexLift f x).isStronglyCartesian
    (chi₁.reindexLift f x).isStronglyCartesian

/-- The forward ambient comparison between two cleavage choices lies over the identity of the
reindexing base object. -/
theorem Reindex.uniqueAmbientIso.hom.isHomLift
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    p.IsHomLift (𝟙 V) (Reindex.uniqueAmbientIso chi₁ chi₂ f x).hom := by
  letI : p.IsStronglyCartesian f (chi₁.cartesianHom f x) :=
    (chi₁.reindexLift f x).isStronglyCartesian
  letI : p.IsStronglyCartesian f (chi₂.cartesianHom f x) :=
    (chi₂.reindexLift f x).isStronglyCartesian
  exact IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift p
    (g := Iso.refl V) (Category.id_comp f).symm
    (chi₂.cartesianHom f x) (chi₁.cartesianHom f x)

/-- The inverse ambient comparison between two cleavage choices lies over the identity of the
reindexing base object. -/
theorem Reindex.uniqueAmbientIso.inv.isHomLift
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    p.IsHomLift (𝟙 V) (Reindex.uniqueAmbientIso chi₁ chi₂ f x).inv := by
  letI : p.IsStronglyCartesian f (chi₁.cartesianHom f x) :=
    (chi₁.reindexLift f x).isStronglyCartesian
  letI : p.IsStronglyCartesian f (chi₂.cartesianHom f x) :=
    (chi₂.reindexLift f x).isStronglyCartesian
  exact IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift p
    (g := Iso.refl V) (Category.id_comp f).symm
    (chi₂.cartesianHom f x) (chi₁.cartesianHom f x)

/-- The canonical isomorphism in the standard fiber between the reindexing objects selected by
two cleavages. Its maps are the unique vertical comparisons of their cartesian arrows. -/
noncomputable def Reindex.uniqueIsoApp
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (chi₁.reindex f).obj x ≅ (chi₂.reindex f).obj x :=
  Fiber.isoMk (Reindex.uniqueAmbientIso chi₁ chi₂ f x)
    (Reindex.uniqueAmbientIso.hom.isHomLift chi₁ chi₂ f x)

/-- The underlying total-category map of the forward choice comparison is the canonical ambient
domain comparison. -/
@[simp]
theorem Reindex.uniqueIsoApp.hom.val
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.uniqueIsoApp chi₁ chi₂ f x).hom.1 =
      (Reindex.uniqueAmbientIso chi₁ chi₂ f x).hom := rfl

/-- The underlying total-category map of the inverse choice comparison is the inverse canonical
ambient domain comparison. -/
@[simp]
theorem Reindex.uniqueIsoApp.inv.val
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.uniqueIsoApp chi₁ chi₂ f x).inv.1 =
      (Reindex.uniqueAmbientIso chi₁ chi₂ f x).inv := rfl

/-- The forward change-of-cleavage comparison identifies the second selected cartesian arrow
with the first. -/
@[reassoc]
theorem Reindex.uniqueIsoApp.hom.fac
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.uniqueIsoApp chi₁ chi₂ f x).hom.1 ≫
        chi₂.cartesianHom f x =
      chi₁.cartesianHom f x := by
  letI : p.IsStronglyCartesian f (chi₁.cartesianHom f x) :=
    (chi₁.reindexLift f x).isStronglyCartesian
  letI : p.IsStronglyCartesian f (chi₂.cartesianHom f x) :=
    (chi₂.reindexLift f x).isStronglyCartesian
  change IsStronglyCartesian.map p f (chi₂.cartesianHom f x)
    (Category.id_comp f).symm (chi₁.cartesianHom f x) ≫ _ = _
  exact IsStronglyCartesian.fac p f _ _ _

/-- The inverse change-of-cleavage comparison identifies the first selected cartesian arrow
with the second. -/
@[reassoc]
theorem Reindex.uniqueIsoApp.inv.fac
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.uniqueIsoApp chi₁ chi₂ f x).inv.1 ≫
        chi₁.cartesianHom f x =
      chi₂.cartesianHom f x := by
  exact (Reindex.uniqueAmbientIso chi₁ chi₂ f x).inv_comp_eq.mpr
    (Reindex.uniqueIsoApp.hom.fac chi₁ chi₂ f x).symm

/-- The forward canonical comparison between two cleavage choices is natural in the fiber
object. -/
theorem Reindex.uniqueIsoApp.hom.naturality
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U)
    {x y : Fiber p U} (phi : x ⟶ y) :
    (chi₁.reindex f).map phi ≫
        (Reindex.uniqueIsoApp chi₁ chi₂ f y).hom =
      (Reindex.uniqueIsoApp chi₁ chi₂ f x).hom ≫
        (chi₂.reindex f).map phi := by
  have map_fac (chi : p.Cleavage) :
      ((chi.reindex f).map phi).1 ≫ chi.cartesianHom f y =
        chi.cartesianHom f x ≫ phi.1 := by
    letI : p.IsStronglyCartesian f (chi.cartesianHom f x) :=
      (chi.reindexLift f x).isStronglyCartesian
    letI : p.IsStronglyCartesian f (chi.cartesianHom f y) :=
      (chi.reindexLift f y).isStronglyCartesian
    letI := phi.2
    change IsStronglyCartesian.map p f (chi.cartesianHom f y)
      (Category.id_comp f).symm (chi.cartesianHom f x ≫ phi.1) ≫ _ = _
    exact IsStronglyCartesian.fac p f _ _ _
  apply Fiber.hom_ext
  refine @IsStronglyCartesian.ext C S _ _ p V U
    (chi₂.reindexObj f y).1 y.1 f (chi₂.cartesianHom f y)
    (chi₂.reindexLift f y).isStronglyCartesian V (chi₁.reindexObj f x).1 (𝟙 V)
    _ _ ((chi₁.reindex f).map phi ≫ (Reindex.uniqueIsoApp chi₁ chi₂ f y).hom).2
    ((Reindex.uniqueIsoApp chi₁ chi₂ f x).hom ≫ (chi₂.reindex f).map phi).2 ?_
  have hleft :
      (((chi₁.reindex f).map phi).1 ≫ (Reindex.uniqueIsoApp chi₁ chi₂ f y).hom.1) ≫
          chi₂.cartesianHom f y = chi₁.cartesianHom f x ≫ phi.1 :=
    (Category.assoc _ _ _).trans
      ((congrArg (((chi₁.reindex f).map phi).1 ≫ ·)
        (Reindex.uniqueIsoApp.hom.fac chi₁ chi₂ f y)).trans (map_fac chi₁))
  have hright :
      ((Reindex.uniqueIsoApp chi₁ chi₂ f x).hom.1 ≫ ((chi₂.reindex f).map phi).1) ≫
          chi₂.cartesianHom f y = chi₁.cartesianHom f x ≫ phi.1 :=
    (Category.assoc _ _ _).trans
      ((congrArg ((Reindex.uniqueIsoApp chi₁ chi₂ f x).hom.1 ≫ ·) (map_fac chi₂)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ phi.1) (Reindex.uniqueIsoApp.hom.fac chi₁ chi₂ f x))))
  exact hleft.trans hright.symm

/-- Naturality of the inverse canonical comparison between two cleavage choices. -/
theorem Reindex.uniqueIsoApp.inv.naturality
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U)
    {x y : Fiber p U} (phi : x ⟶ y) :
    (chi₂.reindex f).map phi ≫
        (Reindex.uniqueIsoApp chi₁ chi₂ f y).inv =
      (Reindex.uniqueIsoApp chi₁ chi₂ f x).inv ≫
        (chi₁.reindex f).map phi := by
  apply (Iso.comp_inv_eq (Reindex.uniqueIsoApp chi₁ chi₂ f y)).2
  rw [Category.assoc, Reindex.uniqueIsoApp.hom.naturality, Iso.inv_hom_id_assoc]

/-- Reindexing functors induced by two cleavages are canonically naturally isomorphic. -/
@[stacks 02XN]
noncomputable def Reindex.uniqueIso
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) :
    chi₁.reindex f ≅ chi₂.reindex f :=
  NatIso.ofComponents (Reindex.uniqueIsoApp chi₁ chi₂ f)
    (fun phi ↦ Reindex.uniqueIsoApp.hom.naturality chi₁ chi₂ f phi)

/-- The forward component of the bundled change-of-cleavage comparison is the canonical
objectwise comparison. -/
@[simp]
theorem Reindex.uniqueIso.hom.app
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.uniqueIso chi₁ chi₂ f).hom.app x =
      (Reindex.uniqueIsoApp chi₁ chi₂ f x).hom := rfl

/-- The inverse component of the bundled change-of-cleavage comparison is the canonical
objectwise inverse comparison. -/
@[simp]
theorem Reindex.uniqueIso.inv.app
    (chi₁ chi₂ : p.Cleavage) {U V : C} (f : V ⟶ U) (x : Fiber p U) :
    (Reindex.uniqueIso chi₁ chi₂ f).inv.app x =
      (Reindex.uniqueIsoApp chi₁ chi₂ f x).inv := rfl

end Functor.Cleavage

end CategoryTheory
