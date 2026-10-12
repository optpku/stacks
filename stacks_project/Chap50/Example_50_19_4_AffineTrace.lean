/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap50.Proposition_50_19_3

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AbsoluteDeRham

/-- The absolute one-form `b₀ db₁` on the top open of `Spec A`. -/
noncomputable def basicOneForm (A : Type u) [CommRing A] (b₀ b₁ : A) :
    (RingedSpace.DeRham.term
      (terminal.from (Spec (CommRingCat.of A))).toLRSHom.toShHom 1).val.obj
        (Opposite.op ⊤) :=
  TopCat.Sheaf.DeRham.basic
    (RingedSpace.DeRham.structureMap
      (terminal.from (Spec (CommRingCat.of A))).toLRSHom.toShHom)
    1 (Opposite.op ⊤) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv b₀)
      (fun _ ↦ (Scheme.ΓSpecIso (CommRingCat.of A)).inv b₁)

/-- `basicOneForm A b₀ b₁` is the canonical affine section representing `b₀ db₁`. -/
theorem basicOneForm_apply (A : Type u) [CommRing A] (b₀ b₁ : A) :
    basicOneForm A b₀ b₁ =
      TopCat.Sheaf.DeRham.basic
        (RingedSpace.DeRham.structureMap
          (terminal.from (Spec (CommRingCat.of A))).toLRSHom.toShHom)
        1 (Opposite.op ⊤) ((Scheme.ΓSpecIso (CommRingCat.of A)).inv b₀)
          (fun _ ↦ (Scheme.ΓSpecIso (CommRingCat.of A)).inv b₁) := sorry

end AbsoluteDeRham

namespace AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.Affine

/-- The degree-one absolute de Rham trace evaluated on the affine form `b₀ db₁`. -/
noncomputable def oneForm (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    [IsFinite (Spec.map (CommRingCat.ofHom φ))]
    [Syntomic (Spec.map (CommRingCat.ofHom φ))] (b₀ b₁ : B) :
    (RingedSpace.DeRham.term
      (terminal.from (Spec (CommRingCat.of A))).toLRSHom.toShHom 1).val.obj
        (Opposite.op ⊤) :=
  (((TraceRule.complexMap r hr (Spec.map (CommRingCat.ofHom φ))).f 1).val.app
      (Opposite.op ⊤)).hom (AbsoluteDeRham.basicOneForm B b₀ b₁)

/-- `oneForm` is evaluation of the degree-one component of `TraceRule.complexMap` on the
canonical affine basic form. -/
theorem oneForm_apply (r : TraceRule.{u}) (hr : IsTraceRule r)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    [IsFinite (Spec.map (CommRingCat.ofHom φ))]
    [Syntomic (Spec.map (CommRingCat.ofHom φ))] (b₀ b₁ : B) :
    oneForm r hr φ b₀ b₁ =
      (((TraceRule.complexMap r hr (Spec.map (CommRingCat.ofHom φ))).f 1).val.app
        (Opposite.op ⊤)).hom (AbsoluteDeRham.basicOneForm B b₀ b₁) := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.Affine
