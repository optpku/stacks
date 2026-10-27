/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# A field-valued point through a specified residue-field equivalence

The residue homomorphism is extracted from the original scheme morphism.
The lifted morphism uses the forward function of the supplied equivalence.
Only its factorization law requires compatibility with the canonical residue map.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.SpecFieldPointFactor

variable {Ω : Type u} [Field Ω] {X V : Scheme.{u}}

/-- The point in the native classification is the image of the original point. -/
theorem classifiedPoint_eq (a : Spec (CommRingCat.of Ω) ⟶ X) :
    ((Scheme.SpecToEquivOfField Ω X) a).1 = a default :=
  (Eq.trans
    (Scheme.fromSpecResidueField_apply ((Scheme.SpecToEquivOfField Ω X) a).1
      (Spec.map ((Scheme.SpecToEquivOfField Ω X) a).2 default)).symm
    (Scheme.Hom.comp_apply (Spec.map ((Scheme.SpecToEquivOfField Ω X) a).2)
      (X.fromSpecResidueField ((Scheme.SpecToEquivOfField Ω X) a).1) default).symm).trans
    (congrArg (fun h : Spec (CommRingCat.of Ω) ⟶ X ↦ h default)
      ((Scheme.SpecToEquivOfField Ω X).left_inv a))

/-- The actual residue homomorphism of `a`, transported to its specified image. -/
def residueHom (a : Spec (CommRingCat.of Ω) ⟶ X) (x : X) (ha : a default = x) :
    X.residueField x →+* Ω :=
  ((X.residueFieldCongr ((classifiedPoint_eq a).trans ha)).inv ≫
    ((Scheme.SpecToEquivOfField Ω X) a).2).hom

/-- The extracted homomorphism reconstructs the original scheme morphism. -/
theorem residueHom_reconstruct (a : Spec (CommRingCat.of Ω) ⟶ X)
    (x : X) (ha : a default = x) :
    Spec.map (CommRingCat.ofHom (residueHom a x ha)) ≫
      X.fromSpecResidueField x = a := by
  let T := (Scheme.SpecToEquivOfField Ω X) a
  let h : T.1 = x := (classifiedPoint_eq a).trans ha
  change Spec.map ((X.residueFieldCongr h).inv ≫ T.2) ≫
    X.fromSpecResidueField x = a
  rw [Spec.map_comp_assoc, Scheme.residueFieldCongr_inv,
    Scheme.residueFieldCongr_fromSpecResidueField]
  exact (Scheme.SpecToEquivOfField Ω X).left_inv a

/-- Compose the extracted homomorphism with the specified forward equivalence. -/
def liftResidueHom (a : Spec (CommRingCat.of Ω) ⟶ X)
    (x : X) (ha : a default = x) (v : V)
    (ε : V.residueField v ≃+* X.residueField x) : V.residueField v →+* Ω :=
  (residueHom a x ha).comp ε.toRingHom

/-- The explicit lift determined by the original point and the supplied equivalence. -/
def lift (a : Spec (CommRingCat.of Ω) ⟶ X)
    (x : X) (ha : a default = x) (v : V)
    (ε : V.residueField v ≃+* X.residueField x) :
    Spec (CommRingCat.of Ω) ⟶ V :=
  Spec.map (CommRingCat.ofHom (liftResidueHom a x ha v ε)) ≫
    V.fromSpecResidueField v

/-- The explicit lift factors the original morphism when the inverse equivalence
is the transported canonical residue map of `q`. -/
theorem lift_comp (a : Spec (CommRingCat.of Ω) ⟶ X)
    (x : X) (ha : a default = x) (v : V)
    (ε : V.residueField v ≃+* X.residueField x) (q : V ⟶ X)
    (hq : q v = x)
    (hε : ε.symm.toRingHom =
      ((X.residueFieldCongr hq).inv ≫ q.residueFieldMap v).hom) :
    lift a x ha v ε ≫ q = a := by
  let Cq := (X.residueFieldCongr hq).inv ≫ q.residueFieldMap v
  have square : Spec.map Cq ≫ X.fromSpecResidueField x =
      V.fromSpecResidueField v ≫ q := by
    dsimp only [Cq]
    rw [Spec.map_comp_assoc, Scheme.residueFieldCongr_inv,
      Scheme.residueFieldCongr_fromSpecResidueField]
    exact q.SpecMap_residueFieldMap_fromSpecResidueField v
  have hcomp : Cq ≫ CommRingCat.ofHom (liftResidueHom a x ha v ε) =
      CommRingCat.ofHom (residueHom a x ha) := by
    ext z
    change (residueHom a x ha) (ε (Cq.hom z)) = (residueHom a x ha) z
    have hz : ε (Cq.hom z) = z := by
      change ε (((X.residueFieldCongr hq).inv ≫ q.residueFieldMap v).hom z) = z
      rw [← hε]
      exact ε.apply_symm_apply z
    exact congrArg (residueHom a x ha) hz
  change (Spec.map (CommRingCat.ofHom (liftResidueHom a x ha v ε)) ≫
    V.fromSpecResidueField v) ≫ q = a
  rw [Category.assoc, ← square, ← Spec.map_comp_assoc]
  exact (congrArg (fun f : X.residueField x ⟶ CommRingCat.of Ω ↦
    Spec.map f ≫ X.fromSpecResidueField x) hcomp).trans
      (residueHom_reconstruct a x ha)

/-- The explicit lift has the specified image point without any hypothesis on `q`. -/
theorem lift_apply (a : Spec (CommRingCat.of Ω) ⟶ X)
    (x : X) (ha : a default = x) (v : V)
    (ε : V.residueField v ≃+* X.residueField x) :
    lift a x ha v ε default = v := by
  change V.fromSpecResidueField v
    (Spec.map (CommRingCat.ofHom (liftResidueHom a x ha v ε)) default) = v
  exact Scheme.fromSpecResidueField_apply v _

end AlgebraicGeometry.Scheme.SpecFieldPointFactor
