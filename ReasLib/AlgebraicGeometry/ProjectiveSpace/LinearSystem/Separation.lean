/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.LinearSystem
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Basic

/-!
# Separation by linear systems

This file defines separation of closed points and tangent vectors by a linear system and records
the resulting very-ampleness and closed-immersion criteria.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- A linear system separates closed points if every ordered pair of distinct closed points has
a section vanishing at the first point and nonvanishing at the second. -/
def SeparatesClosedPoints
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) : Prop :=
  ∀ x y : closedPoints X.left, x ≠ y →
    ∃ s : V,
      ((TopCat.Presheaf.Γgerm L.val.presheaf x.1).hom (ψ s)) ∈
          (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.1)) •
            (⊤ : Submodule (X.left.presheaf.stalk x.1)
              (RingedSpace.stalkModuleCat L x.1)) ∧
        ((TopCat.Presheaf.Γgerm L.val.presheaf y.1).hom (ψ s)) ∉
          (IsLocalRing.maximalIdeal (X.left.presheaf.stalk y.1)) •
            (⊤ : Submodule (X.left.presheaf.stalk y.1)
              (RingedSpace.stalkModuleCat L y.1))

/-- Separation of closed points is the stalkwise vanishing and nonvanishing condition. -/
theorem separatesClosedPoints_iff
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) :
    SeparatesClosedPoints X L ψ ↔
      ∀ x y : closedPoints X.left, x ≠ y →
        ∃ s : V,
          ((TopCat.Presheaf.Γgerm L.val.presheaf x.1).hom (ψ s)) ∈
              (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.1)) •
                (⊤ : Submodule (X.left.presheaf.stalk x.1)
                  (RingedSpace.stalkModuleCat L x.1)) ∧
            ((TopCat.Presheaf.Γgerm L.val.presheaf y.1).hom (ψ s)) ∉
              (IsLocalRing.maximalIdeal (X.left.presheaf.stalk y.1)) •
                (⊤ : Submodule (X.left.presheaf.stalk y.1)
                  (RingedSpace.stalkModuleCat L y.1)) :=
  Iff.rfl

/-- A linear system separates tangent vectors if each nonzero tangent vector at a closed point is
detected by a section vanishing at that point after trivializing the invertible stalk. -/
def SeparatesTangentVectors
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) : Prop :=
  ∀ x : closedPoints X.left,
    ∀ θ : Scheme.Hom.tangentSpaceAt X.hom x.1, θ ≠ 0 →
      ∃ s : V,
        ∃ e : RingedSpace.stalkModuleCat L x.1 ≅
            ModuleCat.of (X.left.presheaf.stalk x.1) (X.left.presheaf.stalk x.1),
          ((TopCat.Presheaf.Γgerm L.val.presheaf x.1).hom (ψ s)) ∈
              (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.1)) •
                (⊤ : Submodule (X.left.presheaf.stalk x.1)
                  (RingedSpace.stalkModuleCat L x.1)) ∧
            θ (e.hom ((TopCat.Presheaf.Γgerm L.val.presheaf x.1).hom (ψ s))) ≠ 0

/-- Separation of tangent vectors is the stalkwise tangent-detection condition. -/
theorem separatesTangentVectors_iff
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) :
    SeparatesTangentVectors X L ψ ↔
      ∀ x : closedPoints X.left,
        ∀ θ : Scheme.Hom.tangentSpaceAt X.hom x.1, θ ≠ 0 →
          ∃ s : V,
            ∃ e : RingedSpace.stalkModuleCat L x.1 ≅
                ModuleCat.of (X.left.presheaf.stalk x.1) (X.left.presheaf.stalk x.1),
              ((TopCat.Presheaf.Γgerm L.val.presheaf x.1).hom (ψ s)) ∈
                  (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.1)) •
                    (⊤ : Submodule (X.left.presheaf.stalk x.1)
                      (RingedSpace.stalkModuleCat L x.1)) ∧
                θ (e.hom ((TopCat.Presheaf.Γgerm L.val.presheaf x.1).hom (ψ s))) ≠ 0 :=
  Iff.rfl

/-- A linear system induces a closed immersion when it generates the invertible module and its
available canonical projective morphism is a closed immersion for every generation proof. -/
def InducesClosedImmersion
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) : Prop :=
  Generates X L ψ ∧
    ∀ (hψ : Generates X L ψ),
      IsClosedImmersion (morphism X L ψ hψ)

/-- Inducing a closed immersion is equivalent to generation together with closed immersion of
every canonical projective morphism obtained from the linear system. -/
theorem inducesClosedImmersion_iff
    (X : Over (Spec (CommRingCat.of k))) (L : X.left.Modules)
    [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L) :
    InducesClosedImmersion X L ψ ↔
      Generates X L ψ ∧
        ∀ (hψ : Generates X L ψ),
          IsClosedImmersion (morphism X L ψ hψ) :=
  Iff.rfl

/-- If a linear system separates closed points of a scheme locally of finite type over a field
with at least two closed points, then it generates the invertible module: for a closed point `x`
choose a closed point `y ≠ x`, so some section vanishes at `y` but not at `x`, and closed points
are dense in the closed non-generated locus. This is the first step of the proof of Stacks 0E8S;
it fails when there is only one closed point, where separation of closed points is vacuous. -/
theorem generates_of_separatesClosedPoints
    (X : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (ψ : ModuleCat.of k V ⟶ Scheme.Hom.globalSectionsMod X.hom L)
    (h_nontrivial : (closedPoints X.left).Nontrivial)
    (h_points : SeparatesClosedPoints X L ψ) :
    Generates X L ψ := sorry

/-- A generating subspace of sections that separates closed points and tangent vectors induces a
closed immersion into its projective scheme.

Stacks 0E8S does not list generation among its hypotheses; its proof derives it from separation
of closed points, which is only valid when `X` has at least two closed points (see
`generates_of_separatesClosedPoints`). For `X = Spec k` and `W = ⊥` both separation conditions
hold vacuously while `W` does not generate, so generation is an explicit premise here. -/
theorem inducesClosedImmersion_of_separates
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (W : Submodule k (Scheme.Hom.globalSectionsMod X.hom L))
    (h_generates : Generates X L (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype))
    (h_points : SeparatesClosedPoints X L
      (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype))
    (h_tangents : SeparatesTangentVectors X L
      (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype)) :
    InducesClosedImmersion X L
      (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype) := sorry

/-- A subspace of sections that separates closed points and tangent vectors makes the invertible
module relatively very ample over the field. -/
theorem relativelyVeryAmple_of_separatesClosedPoints_and_separatesTangentVectors
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (W : Submodule k (Scheme.Hom.globalSectionsMod X.hom L))
    (h_points : SeparatesClosedPoints X L
      (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype))
    (h_tangents : SeparatesTangentVectors X L
      (ConcreteCategory.ofHom (C := ModuleCat k) W.subtype)) :
    RelativelyVeryAmple X.hom L := sorry

end AlgebraicGeometry.ProjectiveSpace.VectorSpace.LinearSystem
