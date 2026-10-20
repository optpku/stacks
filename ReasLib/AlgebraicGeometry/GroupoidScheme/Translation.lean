/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.GroupoidScheme

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- A source section and the identity of the arrow scheme form a composable pair after
pullback along the target map. -/
theorem leftTranslationComposable {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U) :
    (G.t ≫ a) ≫ G.s = (𝟙 G.R) ≫ G.t := by
  -- The source section condition identifies the source of `a ∘ t` with the target of `𝟙`.
  calc
    (G.t ≫ a) ≫ G.s = G.t ≫ (a ≫ G.s) := by simp [Category.assoc]
    _ = G.t := by rw [ha, Category.comp_id]
    _ = (𝟙 G.R) ≫ G.t := by simp

/-- Left translation by a source section of a groupoid scheme. -/
def leftTranslation {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U) : G.R ⟶ G.R :=
  G.compose (G.t ≫ a) (𝟙 G.R) (leftTranslationComposable G a ha)

/-- Left translation is the pointwise composite with the chosen source section. -/
theorem leftTranslation_def {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U) :
    G.leftTranslation a ha =
      G.compose (G.t ≫ a) (𝟙 G.R) (leftTranslationComposable G a ha) := by
  -- This is the defining expression for left translation.
  rfl

/-- Left translation sends the identity section to the translating section. -/
theorem leftTranslation_identity {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U) :
    G.e ≫ G.leftTranslation a ha = a := by
  have compose_precomp {T T' : Over S} (f : T' ⟶ T) (x y : T ⟶ G.R)
      (hxy : x ≫ G.s = y ≫ G.t) :
      f ≫ G.compose x y hxy =
        G.compose (f ≫ x) (f ≫ y)
          (by simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) hxy) := by
    -- Precomposition distributes through the pullback lift defining `G.compose`.
    calc
      f ≫ G.compose x y hxy = (f ≫ pullback.lift x y hxy) ≫ G.c := by
        simp [GroupoidScheme.compose, Category.assoc]
      _ =
          pullback.lift (f ≫ x) (f ≫ y)
            (by simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) hxy) ≫ G.c := by
          congr 1
          apply pullback.hom_ext
          · simp [Category.assoc, pullback.lift_fst]
          · simp [Category.assoc, pullback.lift_snd]
      _ = G.compose (f ≫ x) (f ≫ y)
            (by simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) hxy) := by
          rfl
  -- Evaluate translation at the identity section and reduce to the right-identity law.
  calc
    G.e ≫ G.leftTranslation a ha =
        G.compose ((G.e ≫ G.t) ≫ a) G.e
          (by simpa [Category.assoc, ha, G.identity_target] using
            congrArg (fun k ↦ G.e ≫ k) (G.leftTranslationComposable a ha)) := by
      simpa [leftTranslation, Category.assoc] using
        compose_precomp (f := G.e) (x := G.t ≫ a) (y := 𝟙 G.R)
          (hxy := G.leftTranslationComposable a ha)
    _ = G.compose a G.e
          (by simpa [Category.assoc, ha, G.identity_target]) := by
      simp [G.identity_target]
    _ = a := by
      simpa [Category.assoc, ha, G.identity_target] using
        G.compose_right_identity a
          (by simpa [Category.assoc, ha, G.identity_target])

/-- The underlying residue-field lift is a section of the source map. -/
theorem sourceLiftAtLeft_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {K : Type u} [Field K] (uIso : G.U.left ≅ Spec (.of K)) (r : G.R.left)
    [IsIso (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)] :
    (uIso.hom ≫
          inv (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom) ≫
        G.R.left.fromSpecResidueField r) ≫
      G.s.left = 𝟙 G.U.left := by
  -- Postcompose with `uIso.hom` and cancel the isomorphism to expose `inv ≫ hom`.
  rw [← cancel_mono uIso.hom]
  simp [Category.assoc]

/-- The explicit residue-field lift of a point is a morphism over the base scheme. -/
theorem sourceLiftAtOver {S : Scheme.{u}} (G : GroupoidScheme S)
    {K : Type u} [Field K] (uIso : G.U.left ≅ Spec (.of K)) (r : G.R.left)
    [IsIso (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)] :
    (uIso.hom ≫
          inv (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom) ≫
        G.R.left.fromSpecResidueField r) ≫
      G.R.hom = G.U.hom := by
  -- The raw section identity upgrades to an equality over the base because `G.s` is over `S`.
  calc
    (uIso.hom ≫
          inv (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom) ≫
        G.R.left.fromSpecResidueField r) ≫
        G.R.hom =
      ((uIso.hom ≫
          inv (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom) ≫
        G.R.left.fromSpecResidueField r) ≫
        G.s.left) ≫
          G.U.hom := by
        simp [Category.assoc, Over.w G.s]
    _ = G.U.hom := by
      rw [sourceLiftAtLeft_source, Category.id_comp]

/-- The explicit source section through a residue-field point whose source residue map is
an isomorphism. -/
def sourceLiftAt {S : Scheme.{u}} (G : GroupoidScheme S)
    {K : Type u} [Field K] (uIso : G.U.left ≅ Spec (.of K)) (r : G.R.left)
    [IsIso (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)] : G.U ⟶ G.R :=
  Over.homMk
    (uIso.hom ≫
        inv (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom) ≫
      G.R.left.fromSpecResidueField r)
    (sourceLiftAtOver G uIso r)

/-- The residue-field lift is a section of the source map. -/
theorem sourceLiftAt_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {K : Type u} [Field K] (uIso : G.U.left ≅ Spec (.of K)) (r : G.R.left)
    [IsIso (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)] :
    G.sourceLiftAt uIso r ≫ G.s = 𝟙 G.U := by
  -- The bundled section inherits the underlying source identity proved above.
  apply Over.OverMorphism.ext
  simpa [sourceLiftAt, Category.assoc] using
    G.sourceLiftAtLeft_source uIso r

/-- The residue-field lift sends the closed point corresponding to `U` to the chosen
point of the arrow scheme. -/
theorem sourceLiftAt_point {S : Scheme.{u}} (G : GroupoidScheme S)
    {K : Type u} [Field K] (uIso : G.U.left ≅ Spec (.of K)) (r : G.R.left)
    [IsIso (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)] :
    (G.sourceLiftAt uIso r).left (uIso.inv (IsLocalRing.closedPoint K)) = r := by
  have hu :
      uIso.hom (uIso.inv (IsLocalRing.closedPoint K)) = IsLocalRing.closedPoint K := by
    -- The chosen point of `G.U.left` corresponds to the unique closed point of `Spec K`.
    simpa using congrArg (fun f ↦ f (IsLocalRing.closedPoint K)) uIso.hom_inv_id
  have hclosed :
      inv (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)
          (IsLocalRing.closedPoint K) =
        IsLocalRing.closedPoint (G.R.left.residueField r) := by
    -- Both spectra of fields are subsingletons, so the inverse map sends the closed point
    -- to the unique point.
    exact Subsingleton.elim _ _
  -- Evaluate the explicit composite defining the residue-field lift at the chosen point.
  change
    G.R.left.fromSpecResidueField r
        (inv (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)
          (uIso.hom (uIso.inv (IsLocalRing.closedPoint K)))) = r
  rw [hu, hclosed]
  exact Scheme.fromSpecResidueField_apply r _

/-- Left translation by the explicit source lift of a residue-field point. -/
def leftTranslationAt {S : Scheme.{u}} (G : GroupoidScheme S)
    {K : Type u} [Field K] (uIso : G.U.left ≅ Spec (.of K)) (r : G.R.left)
    [IsIso (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)] : G.R ⟶ G.R :=
  G.leftTranslation (G.sourceLiftAt uIso r) (G.sourceLiftAt_source uIso r)

/-- Translation at a residue-field point is composition with its explicit source lift. -/
theorem leftTranslationAt_def {S : Scheme.{u}} (G : GroupoidScheme S)
    {K : Type u} [Field K] (uIso : G.U.left ≅ Spec (.of K)) (r : G.R.left)
    [IsIso (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)] :
    G.leftTranslationAt uIso r =
      G.compose (G.t ≫ G.sourceLiftAt uIso r) (𝟙 G.R)
        (G.leftTranslationComposable (G.sourceLiftAt uIso r)
          (G.sourceLiftAt_source uIso r)) := by
  -- This is the defining expression for translation by the explicit lift.
  simpa [leftTranslationAt] using
    G.leftTranslation_def (G.sourceLiftAt uIso r) (G.sourceLiftAt_source uIso r)

/-- Translation by a source section with invertible target map is an automorphism. -/
theorem isIso_leftTranslation_of_targetIsIso {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.U ⟶ G.R) (ha : a ≫ G.s = 𝟙 G.U) [IsIso (a ≫ G.t)] :
    IsIso (G.leftTranslation a ha) := by
  let b : G.U ⟶ G.R := inv (a ≫ G.t) ≫ a ≫ G.i
  have hb : b ≫ G.s = 𝟙 G.U := by
    -- Inverting the target map turns `a` into another source section.
    calc
      b ≫ G.s = inv (a ≫ G.t) ≫ a ≫ G.t := by
        simp [b, Category.assoc, G.inverse_source]
      _ = 𝟙 G.U := by
        simp
  have hbTarget : b ≫ G.t = inv (a ≫ G.t) := by
    -- The target of the inverse section is the inverse target automorphism.
    calc
      b ≫ G.t = inv (a ≫ G.t) ≫ a ≫ G.s := by
        simp [b, Category.assoc, G.inverse_target]
      _ = inv (a ≫ G.t) := by
        simpa [Category.assoc, ha]
  have compose_precomp {T T' : Over S} (f : T' ⟶ T) (x y : T ⟶ G.R)
      (hxy : x ≫ G.s = y ≫ G.t) :
      f ≫ G.compose x y hxy =
        G.compose (f ≫ x) (f ≫ y)
          (by simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) hxy) := by
    -- Precomposition distributes through the pullback lift defining `G.compose`.
    calc
      f ≫ G.compose x y hxy = (f ≫ pullback.lift x y hxy) ≫ G.c := by
        simp [GroupoidScheme.compose, Category.assoc]
      _ =
          pullback.lift (f ≫ x) (f ≫ y)
            (by simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) hxy) ≫ G.c := by
          congr 1
          apply pullback.hom_ext
          · simp [Category.assoc, pullback.lift_fst]
          · simp [Category.assoc, pullback.lift_snd]
      _ = G.compose (f ≫ x) (f ≫ y)
            (by simpa [Category.assoc] using congrArg (fun k ↦ f ≫ k) hxy) := by
          rfl
  have hTargetA : G.leftTranslation a ha ≫ G.t = G.t ≫ a ≫ G.t := by
    -- The target of a translated arrow is controlled by the target of `a`.
    simpa [leftTranslation, Category.assoc] using
      G.compose_target (G.t ≫ a) (𝟙 G.R) (G.leftTranslationComposable a ha)
  have hTargetB : G.leftTranslation b hb ≫ G.t = G.t ≫ b ≫ G.t := by
    -- The same target computation applies to the inverse section.
    simpa [leftTranslation, Category.assoc] using
      G.compose_target (G.t ≫ b) (𝟙 G.R) (G.leftTranslationComposable b hb)
  have hInvCompA :
      G.compose (G.t ≫ a ≫ G.i) (G.t ≫ a)
        (by simp [Category.assoc, G.inverse_source]) = G.t ≫ G.e := by
    -- First compose the inverse of `a` with `a` itself.
    simpa [Category.assoc, ha] using
      G.inverse_compose (G.t ≫ a) (by simp [Category.assoc, G.inverse_source])
  have hCompInvA :
      G.compose (G.t ≫ inv (a ≫ G.t) ≫ a) (G.t ≫ b)
        (by simp [b, Category.assoc, ha, hbTarget]) = G.t ≫ G.e := by
    -- Then compose `a` with its inverse section on the left.
    simpa [b, Category.assoc] using
      G.compose_inverse (G.t ≫ inv (a ≫ G.t) ≫ a)
        (by simp [b, Category.assoc, ha, hbTarget])
  have hFirstA : ((G.leftTranslation a ha ≫ G.t) ≫ b) = G.t ≫ a ≫ G.i := by
    -- The first arrow in the composite translation is the inverse of the translating arrow.
    calc
      ((G.leftTranslation a ha ≫ G.t) ≫ b) = (G.t ≫ a ≫ G.t) ≫ b := by
        rw [hTargetA]
      _ = G.t ≫ a ≫ G.i := by
        simp [b, Category.assoc]
  have hFirstB : ((G.leftTranslation b hb ≫ G.t) ≫ a) = G.t ≫ inv (a ≫ G.t) ≫ a := by
    -- Dually, the first arrow for the opposite composite is `a` after the inverse target map.
    calc
      ((G.leftTranslation b hb ≫ G.t) ≫ a) = (G.t ≫ b ≫ G.t) ≫ a := by
        rw [hTargetB]
      _ = G.t ≫ inv (a ≫ G.t) ≫ a := by
        simp [b, hbTarget]
  refine ⟨⟨G.leftTranslation b hb, ?_, ?_⟩⟩
  · -- The inverse section cancels translation on the right.
    calc
      G.leftTranslation a ha ≫ G.leftTranslation b hb =
          G.compose ((G.leftTranslation a ha ≫ G.t) ≫ b) (G.leftTranslation a ha)
            (by
              simpa [Category.assoc, hb] using
                congrArg (fun k ↦ G.leftTranslation a ha ≫ k)
                  (G.leftTranslationComposable b hb)) := by
            simpa [leftTranslation, Category.assoc] using
              compose_precomp (f := G.leftTranslation a ha) (x := G.t ≫ b) (y := 𝟙 G.R)
                (hxy := G.leftTranslationComposable b hb)
      _ = G.compose (G.t ≫ a ≫ G.i) (G.leftTranslation a ha)
            (by
              calc
                (G.t ≫ a ≫ G.i) ≫ G.s = G.t ≫ a ≫ G.t := by
                  simp [Category.assoc, G.inverse_source]
                _ = G.leftTranslation a ha ≫ G.t := by
                  symm
                  exact hTargetA) := by
            simpa [hFirstA]
      _ = G.compose
            (G.compose (G.t ≫ a ≫ G.i) (G.t ≫ a)
              (by simp [Category.assoc, G.inverse_source]))
            (𝟙 G.R)
            (by
              calc
                G.compose (G.t ≫ a ≫ G.i) (G.t ≫ a)
                    (by simp [Category.assoc, G.inverse_source]) ≫ G.s =
                    (G.t ≫ G.e) ≫ G.s := by
                      rw [hInvCompA]
                _ = G.t := by simp [Category.assoc, G.identity_source]
                _ = (𝟙 G.R) ≫ G.t := by simp) := by
            symm
            simpa [leftTranslation] using G.compose_assoc
              (G.t ≫ a ≫ G.i) (G.t ≫ a) (𝟙 G.R)
              (by simp [Category.assoc, G.inverse_source])
              (G.leftTranslationComposable a ha)
              (by
                calc
                  G.compose (G.t ≫ a ≫ G.i) (G.t ≫ a)
                      (by simp [Category.assoc, G.inverse_source]) ≫ G.s =
                      (G.t ≫ G.e) ≫ G.s := by
                        rw [hInvCompA]
                  _ = G.t := by simp [Category.assoc, G.identity_source]
                  _ = (𝟙 G.R) ≫ G.t := by simp)
              (by
                calc
                  (G.t ≫ a ≫ G.i) ≫ G.s = G.t ≫ a ≫ G.t := by
                    simp [Category.assoc, G.inverse_source]
                  _ = G.leftTranslation a ha ≫ G.t := by
                    symm
                    exact hTargetA)
      _ = G.compose (G.t ≫ G.e) (𝟙 G.R)
            (by simp [Category.assoc, G.identity_source]) := by
            simpa [hInvCompA]
      _ = 𝟙 G.R := by
            simpa [Category.assoc] using
              G.compose_left_identity (𝟙 G.R) (by simp [Category.assoc, G.identity_source])
  · -- The inverse section also cancels translation on the left.
    calc
      G.leftTranslation b hb ≫ G.leftTranslation a ha =
          G.compose ((G.leftTranslation b hb ≫ G.t) ≫ a) (G.leftTranslation b hb)
            (by
              simpa [Category.assoc, ha] using
                congrArg (fun k ↦ G.leftTranslation b hb ≫ k)
                  (G.leftTranslationComposable a ha)) := by
            simpa [leftTranslation, Category.assoc] using
              compose_precomp (f := G.leftTranslation b hb) (x := G.t ≫ a) (y := 𝟙 G.R)
                (hxy := G.leftTranslationComposable a ha)
      _ = G.compose (G.t ≫ inv (a ≫ G.t) ≫ a) (G.leftTranslation b hb)
            (by
              calc
                (G.t ≫ inv (a ≫ G.t) ≫ a) ≫ G.s = G.t ≫ inv (a ≫ G.t) := by
                  simp [Category.assoc, ha]
                _ = G.t ≫ b ≫ G.t := by
                  simp [hbTarget]
                _ = G.leftTranslation b hb ≫ G.t := by
                  symm
                  exact hTargetB) := by
            simpa [hFirstB]
      _ = G.compose
            (G.compose (G.t ≫ inv (a ≫ G.t) ≫ a) (G.t ≫ b)
              (by simp [b, Category.assoc, ha, hbTarget]))
            (𝟙 G.R)
            (by
              calc
                G.compose (G.t ≫ inv (a ≫ G.t) ≫ a) (G.t ≫ b)
                    (by simp [b, Category.assoc, ha, hbTarget]) ≫ G.s =
                    (G.t ≫ G.e) ≫ G.s := by
                      rw [hCompInvA]
                _ = G.t := by simp [Category.assoc, G.identity_source]
                _ = (𝟙 G.R) ≫ G.t := by simp) := by
            symm
            simpa [leftTranslation] using G.compose_assoc
              (G.t ≫ inv (a ≫ G.t) ≫ a) (G.t ≫ b) (𝟙 G.R)
              (by simp [b, Category.assoc, ha, hbTarget])
              (G.leftTranslationComposable b hb)
              (by
                calc
                  G.compose (G.t ≫ inv (a ≫ G.t) ≫ a) (G.t ≫ b)
                      (by simp [b, Category.assoc, ha, hbTarget]) ≫ G.s =
                      (G.t ≫ G.e) ≫ G.s := by
                        rw [hCompInvA]
                  _ = G.t := by simp [Category.assoc, G.identity_source]
                  _ = (𝟙 G.R) ≫ G.t := by simp)
              (by
                calc
                  (G.t ≫ inv (a ≫ G.t) ≫ a) ≫ G.s = G.t ≫ inv (a ≫ G.t) := by
                    simp [Category.assoc, ha]
                  _ = G.t ≫ b ≫ G.t := by
                    simp [hbTarget]
                  _ = G.leftTranslation b hb ≫ G.t := by
                    symm
                    exact hTargetB)
      _ = G.compose (G.t ≫ G.e) (𝟙 G.R)
            (by simp [Category.assoc, G.identity_source]) := by
            simpa [hCompInvA]
      _ = 𝟙 G.R := by
            simpa [Category.assoc] using
      G.compose_left_identity (𝟙 G.R) (by simp [Category.assoc, G.identity_source])

/-- Left translation by a residue-field point is an isomorphism when its source and target
residue maps are isomorphisms. -/
theorem isIso_leftTranslationAt {S : Scheme.{u}} (G : GroupoidScheme S)
    {K : Type u} [Field K] (uIso : G.U.left ≅ Spec (.of K)) (r : G.R.left)
    [IsIso (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)]
    [IsIso (G.R.left.fromSpecResidueField r ≫ G.t.left ≫ uIso.hom)] :
    IsIso (G.leftTranslationAt uIso r) := by
  have hTargetComp :
      Over.Hom.left (G.sourceLiftAt uIso r ≫ G.t) ≫ uIso.hom =
        uIso.hom ≫
          inv (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom) ≫
            (G.R.left.fromSpecResidueField r ≫ G.t.left ≫ uIso.hom) := by
    simp [sourceLiftAt, Category.assoc]
  have hTargetLeftIso : IsIso (Over.Hom.left (G.sourceLiftAt uIso r ≫ G.t)) := by
    rw [show Over.Hom.left (G.sourceLiftAt uIso r ≫ G.t) =
        (Over.Hom.left (G.sourceLiftAt uIso r ≫ G.t) ≫ uIso.hom) ≫ uIso.inv by
          simp [Category.assoc]]
    rw [hTargetComp]
    infer_instance
  have hTargetIso : IsIso (G.sourceLiftAt uIso r ≫ G.t) := by
    -- Local instance justification (proof-local temporary data): reflection through `Over.forget`.
    letI : IsIso ((Over.forget S).map (G.sourceLiftAt uIso r ≫ G.t)) := by
      simpa using hTargetLeftIso
    exact isIso_of_reflects_iso (G.sourceLiftAt uIso r ≫ G.t) (Over.forget S)
  -- Local instance justification (proof-local temporary data): consumption by the generic translation theorem.
  letI : IsIso (G.sourceLiftAt uIso r ≫ G.t) := hTargetIso
  simpa [leftTranslationAt] using
    G.isIso_leftTranslation_of_targetIsIso
      (G.sourceLiftAt uIso r) (G.sourceLiftAt_source uIso r)

/-- Left translation at a residue-field point sends the identity section to the
corresponding explicit source lift. -/
theorem leftTranslationAt_identity {S : Scheme.{u}} (G : GroupoidScheme S)
    {K : Type u} [Field K] (uIso : G.U.left ≅ Spec (.of K)) (r : G.R.left)
    [IsIso (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)] :
    G.e ≫ G.leftTranslationAt uIso r = G.sourceLiftAt uIso r := by
  simpa [leftTranslationAt] using
    G.leftTranslation_identity (G.sourceLiftAt uIso r) (G.sourceLiftAt_source uIso r)

/-- Left translation by a residue-field point sends the distinguished identity point to
that point. -/
theorem leftTranslationAt_mapsIdentity {S : Scheme.{u}} (G : GroupoidScheme S)
    {K : Type u} [Field K] (uIso : G.U.left ≅ Spec (.of K)) (r : G.R.left)
    [IsIso (G.R.left.fromSpecResidueField r ≫ G.s.left ≫ uIso.hom)]
    [IsIso (G.R.left.fromSpecResidueField r ≫ G.t.left ≫ uIso.hom)] :
    (G.leftTranslationAt uIso r).left
        (G.e.left (uIso.inv (IsLocalRing.closedPoint K))) = r := by
  have h_identity :
      (G.leftTranslationAt uIso r).left
          (G.e.left (uIso.inv (IsLocalRing.closedPoint K))) =
        (G.sourceLiftAt uIso r).left (uIso.inv (IsLocalRing.closedPoint K)) := by
    simpa using
      congrArg (fun f ↦ f (uIso.inv (IsLocalRing.closedPoint K)))
        (congrArg Over.Hom.left (G.leftTranslationAt_identity uIso r))
  exact h_identity.trans (G.sourceLiftAt_point uIso r)

end AlgebraicGeometry.GroupoidScheme
