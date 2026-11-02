/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.Differentials

/-!
# Maps on relative tangent spaces

This file defines the maps on relative cotangent and tangent spaces induced by
a morphism of schemes over a common base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism of schemes over a common base induces a map on relative Kähler
differentials at each point. -/
noncomputable def relativeCotangentMapAt
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    -- Local instance justification (defeq pin): restrict the source cotangent module along
    -- the stalk map through which the induced differential map is linear.
    let _ : Module (Y.presheaf.stalk (f x))
        (CommRingCat.KaehlerDifferential ((f ≫ g).stalkMap x)) :=
      Module.compHom _ (f.stalkMap x).hom
    CommRingCat.KaehlerDifferential (g.stalkMap (f x)) →ₗ[Y.presheaf.stalk (f x)]
      CommRingCat.KaehlerDifferential ((f ≫ g).stalkMap x) :=
  ModuleCat.Hom.hom <|
    @CommRingCat.KaehlerDifferential.map
      (S.presheaf.stalk ((f ≫ g) x))
      (Y.presheaf.stalk (f x))
      (S.presheaf.stalk ((f ≫ g) x))
      (X.presheaf.stalk x)
      (g.stalkMap (f x))
      ((f ≫ g).stalkMap x)
      (𝟙 _)
      (f.stalkMap x)
      (by rw [Category.id_comp, stalkMap_comp]; rfl)

/-- If the induced residue-field map at a point is bijective, a morphism of schemes over a
common base induces a linear map on relative tangent spaces. -/
noncomputable def relativeTangentMapAt
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hκ : Function.Bijective (Scheme.Hom.residueFieldMap f x).hom) :
    -- Local instance justification (noncanonical choice): restrict the source tangent-space
    -- action along the residue-field equivalence specified by the explicit hypothesis `hκ`.
    let _ : Module (Y.residueField (f x)) (tangentSpaceAt (f ≫ g) x) :=
      Module.compHom (tangentSpaceAt (f ≫ g) x)
        (RingEquiv.ofBijective (Scheme.Hom.residueFieldMap f x).hom hκ).toRingHom
    tangentSpaceAt (f ≫ g) x →ₗ[Y.residueField (f x)] tangentSpaceAt g (f x) :=
  let eκ := RingEquiv.ofBijective (Scheme.Hom.residueFieldMap f x).hom hκ
  -- Local instance justification (noncanonical choice): use the residue-field equivalence
  -- specified by `hκ` to restrict scalars on the source tangent space.
  let _ : Module (Y.residueField (f x)) (tangentSpaceAt (f ≫ g) x) :=
    Module.compHom (tangentSpaceAt (f ≫ g) x) eκ.toRingHom
  -- Local instance justification (defeq pin): use the target stalk algebra defining the
  -- codomain relative tangent space.
  let _ : Algebra (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) :=
    (g.stalkMap (f x)).hom.toAlgebra
  -- Local instance justification (defeq pin): use the target residue algebra defining the
  -- codomain relative tangent space.
  let _ : Algebra (Y.presheaf.stalk (f x)) (Y.residueField (f x)) :=
    (Y.residue (f x)).hom.toAlgebra
  -- Local instance justification (defeq pin): use the composite target-stalk action defining
  -- the codomain relative tangent space.
  let _ : Algebra (S.presheaf.stalk (g (f x))) (Y.residueField (f x)) :=
    ((Y.residue (f x)).hom.comp (g.stalkMap (f x)).hom).toAlgebra
  -- Pin the source derivation's scalar actions to the defining stalk maps.
  letI : Algebra (S.presheaf.stalk ((f ≫ g) x)) (X.presheaf.stalk x) :=
    ((f ≫ g).stalkMap x).hom.toAlgebra
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  letI : Algebra (S.presheaf.stalk ((f ≫ g) x)) (X.residueField x) :=
    ((X.residue x).hom.comp ((f ≫ g).stalkMap x).hom).toAlgebra
  have hres (a : Y.presheaf.stalk (f x)) :
      eκ ((Y.residue (f x)).hom a) =
        (X.residue x).hom ((f.stalkMap x).hom a) :=
    congrArg (fun k => k.hom a) (residue_residueFieldMap f x)
  { toFun := fun D ↦
      { toFun := fun a ↦ eκ.symm (D ((f.stalkMap x).hom a))
        map_add' := by intros; simp only [map_add]
        map_smul' := by
          intro r a
          have hst : (f.stalkMap x).hom ((g.stalkMap (f x)).hom r) =
              ((f ≫ g).stalkMap x).hom r := by
            rw [stalkMap_comp]
            rfl
          change eκ.symm (D ((f.stalkMap x).hom ((g.stalkMap (f x)).hom r * a))) =
            (Y.residue (f x)).hom ((g.stalkMap (f x)).hom r) *
              eκ.symm (D ((f.stalkMap x).hom a))
          rw [map_mul, hst]
          have hD := D.map_smul r ((f.stalkMap x).hom a)
          change D (((f ≫ g).stalkMap x).hom r * (f.stalkMap x).hom a) =
            (X.residue x).hom (((f ≫ g).stalkMap x).hom r) *
              D ((f.stalkMap x).hom a) at hD
          rw [hD, ← hst, ← hres, map_mul, eκ.symm_apply_apply]
        map_one_eq_zero' := by simp
        leibniz' := by
          intro a b
          change eκ.symm (D ((f.stalkMap x).hom (a * b))) =
            (Y.residue (f x)).hom a * eκ.symm (D ((f.stalkMap x).hom b)) +
              (Y.residue (f x)).hom b * eκ.symm (D ((f.stalkMap x).hom a))
          rw [map_mul, D.leibniz]
          change eκ.symm ((X.residue x).hom ((f.stalkMap x).hom a) *
              D ((f.stalkMap x).hom b) +
            (X.residue x).hom ((f.stalkMap x).hom b) * D ((f.stalkMap x).hom a)) = _
          rw [← hres a, ← hres b, map_add, map_mul, map_mul,
            eκ.symm_apply_apply, eκ.symm_apply_apply] }
    map_add' := by
      intro D E
      apply Derivation.ext
      intro a
      exact map_add eκ.symm _ _
    map_smul' := by
      intro c D
      apply Derivation.ext
      intro a
      change eκ.symm (eκ c * D ((f.stalkMap x).hom a)) =
        c * eκ.symm (D ((f.stalkMap x).hom a))
      rw [map_mul, eκ.symm_apply_apply] }

/-- Evaluating the induced tangent map restricts a tangent vector along the stalk map and
transports its value through the inverse residue-field equivalence. -/
theorem relativeTangentMapAt_apply
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hκ : Function.Bijective (Scheme.Hom.residueFieldMap f x).hom)
    (D : tangentSpaceAt (f ≫ g) x) (a : Y.presheaf.stalk (f x)) :
    relativeTangentMapAt f g x hκ D a =
      (RingEquiv.ofBijective (Scheme.Hom.residueFieldMap f x).hom hκ).symm
        (D ((f.stalkMap x).hom a)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Under the canonical identification of relative tangent spaces with linear duals of Kähler
differentials, the induced tangent map is pointwise dual to the induced cotangent map. -/
theorem relativeTangentMapAt_dual
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (x : X)
    (hκ : Function.Bijective (Scheme.Hom.residueFieldMap f x).hom)
    (D : tangentSpaceAt (f ≫ g) x)
    (ω : CommRingCat.KaehlerDifferential (g.stalkMap (f x))) :
    relativeTangentSpaceLinearDual g (f x) (relativeTangentMapAt f g x hκ D) ω =
      (RingEquiv.ofBijective (Scheme.Hom.residueFieldMap f x).hom hκ).symm
        (relativeTangentSpaceLinearDual (f ≫ g) x D
          (relativeCotangentMapAt f g x ω)) := by
  letI : Algebra (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) :=
    (g.stalkMap (f x)).hom.toAlgebra
  let eκ := RingEquiv.ofBijective (Scheme.Hom.residueFieldMap f x).hom hκ
  -- Pin the source derivation's scalar actions to the defining stalk maps.
  letI : Algebra (S.presheaf.stalk ((f ≫ g) x)) (X.presheaf.stalk x) :=
    ((f ≫ g).stalkMap x).hom.toAlgebra
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  letI : Algebra (S.presheaf.stalk ((f ≫ g) x)) (X.residueField x) :=
    ((X.residue x).hom.comp ((f ≫ g).stalkMap x).hom).toAlgebra
  letI : Algebra (Y.presheaf.stalk (f x)) (Y.residueField (f x)) :=
    (Y.residue (f x)).hom.toAlgebra
  letI : Algebra (S.presheaf.stalk (g (f x))) (Y.residueField (f x)) :=
    ((Y.residue (f x)).hom.comp (g.stalkMap (f x)).hom).toAlgebra
  letI : IsScalarTower (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))
      (Y.residueField (f x)) := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower (S.presheaf.stalk ((f ≫ g) x)) (X.presheaf.stalk x)
      (X.residueField x) := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module (Y.presheaf.stalk (f x))
      (CommRingCat.KaehlerDifferential ((f ≫ g).stalkMap x)) :=
    Module.compHom _ (f.stalkMap x).hom
  have hres (a : Y.presheaf.stalk (f x)) :
      eκ ((Y.residue (f x)).hom a) =
        (X.residue x).hom ((f.stalkMap x).hom a) :=
    congrArg (fun k => k.hom a) (residue_residueFieldMap f x)
  change KaehlerDifferential (S.presheaf.stalk (g (f x)))
    (Y.presheaf.stalk (f x)) at ω
  have hω : ω ∈ Submodule.span (Y.presheaf.stalk (f x))
      (Set.range (KaehlerDifferential.D (S.presheaf.stalk (g (f x)))
        (Y.presheaf.stalk (f x)))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hω
  · rintro _ ⟨a, rfl⟩
    change (relativeTangentMapAt f g x hκ D).liftKaehlerDifferential
        (KaehlerDifferential.D _ _ a) =
      eκ.symm (D.liftKaehlerDifferential (relativeCotangentMapAt f g x
        (CommRingCat.KaehlerDifferential.d a)))
    have hmap : relativeCotangentMapAt f g x (CommRingCat.KaehlerDifferential.d a) =
        CommRingCat.KaehlerDifferential.d ((f.stalkMap x).hom a) :=
      CommRingCat.KaehlerDifferential.map_d _ a
    rw [hmap]
    change (relativeTangentMapAt f g x hκ D).liftKaehlerDifferential
        (KaehlerDifferential.D _ _ a) =
      eκ.symm (D.liftKaehlerDifferential
        (KaehlerDifferential.D _ _ ((f.stalkMap x).hom a)))
    rw [Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    rfl
  · simp
  · intro a b _ _ ha hb
    simp only [map_add, ha, hb]
  · intro a ω _ hω
    rw [map_smul, (relativeCotangentMapAt f g x).map_smul]
    change (Y.residue (f x)).hom a *
        relativeTangentSpaceLinearDual g (f x) (relativeTangentMapAt f g x hκ D) ω =
      eκ.symm (relativeTangentSpaceLinearDual (f ≫ g) x D
        ((f.stalkMap x).hom a • relativeCotangentMapAt f g x ω))
    rw [map_smul]
    change _ = eκ.symm ((X.residue x).hom ((f.stalkMap x).hom a) * _)
    rw [← hres, map_mul, eκ.symm_apply_apply]
    exact congrArg (fun z => (Y.residue (f x)).hom a * z) hω

end AlgebraicGeometry.Scheme.Hom
