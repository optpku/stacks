module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus
public import ReasLib.CategoryTheory.Limits.Shapes.Pullback.Sections

/-!
# Source loci for groupoid schemes

This module records descent of a morphism-property source locus along the target pullback of a
groupoid scheme.
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The `P`-source locus of the source map from a target pullback of a groupoid scheme descends
to an open of the base-changed object scheme. -/
theorem exists_open_preimage_eq_sourceLocus {S U' : Scheme.{u}}
    (G : GroupoidScheme S)
    (g : U' ⟶ G.U.left) (P Q R : MorphismProperty Scheme.{u}) (hRQ : R ≤ Q)
    [Q.IsStableUnderBaseChange] [Q.IsStableUnderComposition]
    (h_largest : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Q f →
      IsGreatest {W : X.Opens | P (W.ι ≫ f)} (P.sourceLocus f))
    (h_baseChange : ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {b : Y' ⟶ Y}
      {p : X' ⟶ X} {f' : X' ⟶ Y'}, Q f → R b → IsPullback p f' f b →
      p ⁻¹ᵁ P.sourceLocus f = P.sourceLocus f')
    (hs : R G.s.left) (ht : R G.t.left) (hg : Q g) :
    ∃ W : U'.Opens,
      pullback.fst g G.t.left ⁻¹ᵁ W =
        P.sourceLocus (pullback.snd g G.t.left ≫ G.s.left) := by
  let π : pullback g G.t.left ⟶ U' := pullback.fst g G.t.left
  let h : pullback g G.t.left ⟶ G.U.left := pullback.snd g G.t.left ≫ G.s.left
  let V : (pullback g G.t.left).Opens := P.sourceLocus h
  -- The pullback source map has `Q`, so the source-locus comparison applies.
  have _hQh : Q h := by
    have hsQ : Q G.s.left := hRQ _ hs
    have hgPullback : Q (pullback.snd g G.t.left) := Q.pullback_snd g G.t.left hg
    simpa [h] using Q.comp_mem (pullback.snd g G.t.left) G.s.left hgPullback hsQ
  let splitTarget : SplitEpi G.t.left :=
    { section_ := G.e.left
      id := by
        simpa using congrArg Over.Hom.left G.identity_target }
  let σ : U' ⟶ pullback g G.t.left := (CategoryTheory.SplitEpi.pullbackFst splitTarget g).section_
  have hσ : σ ≫ π = 𝟙 U' := by
    simpa [σ, π] using (CategoryTheory.SplitEpi.pullbackFst splitTarget g).id
  -- Compare the two fiber projections via the common-target pullback and transport once across
  -- the scheme-level target-comparison isomorphism.
  have hfiberEq : pullback.fst π π ⁻¹ᵁ V = pullback.snd π π ⁻¹ᵁ V := by
    have hπ :
        π ≫ g = pullback.snd g G.t.left ≫ G.t.left := by
      simpa [π] using (pullback.condition (f := g) (g := G.t.left))
    let r₁ : pullback π π ⟶ G.R.left :=
      pullback.fst π π ≫ pullback.snd g G.t.left
    let r₂ : pullback π π ⟶ G.R.left :=
      pullback.snd π π ≫ pullback.snd g G.t.left
    have hr :
        r₁ ≫ G.t.left = r₂ ≫ G.t.left := by
      calc
        r₁ ≫ G.t.left = pullback.fst π π ≫ π ≫ g := by
          simp [r₁, hπ, Category.assoc]
        _ = pullback.snd π π ≫ π ≫ g := by
          exact congrArg (fun k ↦ k ≫ g) (pullback.condition (f := π) (g := π))
        _ = r₂ ≫ G.t.left := by
          simp [r₂, hπ, Category.assoc]
    let rho : pullback π π ⟶ pullback G.t.left G.t.left :=
      pullback.lift r₁ r₂ hr
    have hRhoFst :
        IsPullback (pullback.fst π π) rho
          (pullback.snd g G.t.left) (pullback.fst G.t.left G.t.left) := by
      have hOuterFst :
          IsPullback r₂ (pullback.fst π π) G.t.left (pullback.snd g G.t.left ≫ G.t.left) := by
        have hPaste :
            IsPullback (pullback.fst π π)
              (pullback.snd π π ≫ pullback.snd g G.t.left) (π ≫ g) G.t.left := by
          simpa [Category.assoc] using
            (IsPullback.of_hasPullback π π).paste_vert
              (IsPullback.of_hasPullback g G.t.left)
        simpa [r₂, Category.assoc, hπ] using hPaste.flip
      have hRhoDef :
          ((IsPullback.of_hasPullback G.t.left G.t.left).flip).lift
              (pullback.snd π π ≫ pullback.snd g G.t.left)
              (pullback.fst π π ≫ pullback.snd g G.t.left) hr.symm = rho := by
        apply pullback.hom_ext
        · simpa [rho, r₁, r₂] using (pullback.lift_fst r₁ r₂ hr).symm
        · simpa [rho, r₁, r₂] using (pullback.lift_snd r₁ r₂ hr).symm
      have hRho :
          IsPullback rho (pullback.fst π π)
            (pullback.fst G.t.left G.t.left) (pullback.snd g G.t.left) := by
        simpa [r₁, r₂, hRhoDef] using
          IsPullback.of_right' hOuterFst (IsPullback.of_hasPullback G.t.left G.t.left).flip
      exact hRho.flip
    have hRhoSnd :
        IsPullback (pullback.snd π π) rho
          (pullback.snd g G.t.left) (pullback.snd G.t.left G.t.left) := by
      have hOuterSnd :
          IsPullback r₁ (pullback.snd π π) G.t.left (pullback.snd g G.t.left ≫ G.t.left) := by
        have hPaste :
            IsPullback (pullback.snd π π)
              (pullback.fst π π ≫ pullback.snd g G.t.left) (π ≫ g) G.t.left := by
          simpa [Category.assoc] using
            ((IsPullback.of_hasPullback π π).flip).paste_vert
              (IsPullback.of_hasPullback g G.t.left)
        simpa [r₁, Category.assoc, hπ] using hPaste.flip
      have hRhoDef :
          (IsPullback.of_hasPullback G.t.left G.t.left).lift
              (pullback.fst π π ≫ pullback.snd g G.t.left)
              (pullback.snd π π ≫ pullback.snd g G.t.left) hr = rho := by
        apply pullback.hom_ext
        · simpa [rho, r₁, r₂] using (pullback.lift_fst r₁ r₂ hr).symm
        · simpa [rho, r₁, r₂] using (pullback.lift_snd r₁ r₂ hr).symm
      have hRho :
          IsPullback rho (pullback.snd π π)
            (pullback.snd G.t.left G.t.left) (pullback.snd g G.t.left) := by
        simpa [r₁, r₂, hRhoDef] using
          IsPullback.of_right' hOuterSnd (IsPullback.of_hasPullback G.t.left G.t.left)
      exact hRho.flip
    let e : (pullback G.s G.t).left ≅ pullback G.t.left G.t.left :=
      (Over.forget S).mapIso G.targetComparisonIso.symm ≪≫
        PreservesPullback.iso (Over.forget S) G.t G.t
    have hEFst :
        e.hom ≫ pullback.fst G.t.left G.t.left =
          Over.Hom.left (pullback.fst G.s G.t) := by
      have hTargetComparisonInvFst :
          G.targetComparisonInv ≫ pullback.fst G.t G.t = pullback.fst G.s G.t := by
        exact G.targetComparisonInv_fst
      change ((Over.forget S).mapIso G.targetComparisonIso.symm).hom ≫
          (PreservesPullback.iso (Over.forget S) G.t G.t).hom ≫
          pullback.fst G.t.left G.t.left = Over.Hom.left (pullback.fst G.s G.t)
      calc
        Over.Hom.left G.targetComparisonIso.inv ≫
            pullbackComparison (Over.forget S) G.t G.t ≫
            pullback.fst G.t.left G.t.left =
          Over.Hom.left G.targetComparisonIso.inv ≫
            Over.Hom.left (pullback.fst G.t G.t) := by
              simpa using congrArg
                (fun f ↦ Over.Hom.left G.targetComparisonIso.inv ≫ f)
                (PreservesPullback.iso_hom_fst (Over.forget S) G.t G.t)
        _ = Over.Hom.left (pullback.fst G.s G.t) := by
          simpa [targetComparisonIso_inv] using congrArg Over.Hom.left hTargetComparisonInvFst
    have hEComp :
        e.hom ≫ pullback.snd G.t.left G.t.left = G.c.left := by
      change ((Over.forget S).mapIso G.targetComparisonIso.symm).hom ≫
          (PreservesPullback.iso (Over.forget S) G.t G.t).hom ≫
          pullback.snd G.t.left G.t.left = G.c.left
      calc
        Over.Hom.left G.targetComparisonIso.inv ≫
            pullbackComparison (Over.forget S) G.t G.t ≫
            pullback.snd G.t.left G.t.left =
          Over.Hom.left G.targetComparisonIso.inv ≫
            Over.Hom.left (pullback.snd G.t G.t) := by
              simpa using congrArg
                (fun f ↦ Over.Hom.left G.targetComparisonIso.inv ≫ f)
                (PreservesPullback.iso_hom_snd (Over.forget S) G.t G.t)
        _ = G.c.left := by
          simpa [targetComparisonIso_inv] using congrArg Over.Hom.left
            G.targetComparisonInv_snd
    have hEInvFst :
        e.inv ≫ Over.Hom.left (pullback.fst G.s G.t) =
          pullback.fst G.t.left G.t.left := by
      calc
        e.inv ≫ Over.Hom.left (pullback.fst G.s G.t) =
            e.inv ≫ e.hom ≫ pullback.fst G.t.left G.t.left := by
              rw [hEFst]
        _ = pullback.fst G.t.left G.t.left := by
              simp
    have hEInvComp :
        e.inv ≫ G.c.left = pullback.snd G.t.left G.t.left := by
      calc
        e.inv ≫ G.c.left =
            e.inv ≫ e.hom ≫ pullback.snd G.t.left G.t.left := by
              rw [hEComp]
        _ = pullback.snd G.t.left G.t.left := by
              simp
    let deltaComp : pullback π π ⟶ (pullback G.s G.t).left := rho ≫ e.inv
    let delta : pullback π π ⟶ G.R.left :=
      deltaComp ≫ Over.Hom.left (pullback.snd G.s G.t)
    have hDeltaCompFst :
        IsPullback (pullback.fst π π) deltaComp
          (pullback.snd g G.t.left) (Over.Hom.left (pullback.fst G.s G.t)) := by
      refine hRhoFst.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · simp [deltaComp]
      · simp
      · simpa using hEInvFst.symm
    have hDeltaCompComp :
        IsPullback (pullback.snd π π) deltaComp
          (pullback.snd g G.t.left) G.c.left := by
      refine hRhoSnd.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · simp [deltaComp]
      · simp
      · simpa using hEInvComp.symm
    have hProjection :
        IsPullback (Over.Hom.left (pullback.fst G.s G.t))
          (Over.Hom.left (pullback.snd G.s G.t)) G.s.left G.t.left := by
      simpa using G.fstSndIsPullback.map (Over.forget S)
    have hComp :
        IsPullback G.c.left
          (Over.Hom.left (pullback.snd G.s G.t)) G.s.left G.s.left := by
      simpa using G.compSndIsPullback.map (Over.forget S)
    have hFstBase :
        IsPullback (pullback.fst π π) delta h G.t.left := by
      simpa [delta, deltaComp, h, Category.assoc] using hDeltaCompFst.paste_vert hProjection
    have hSndBase :
        IsPullback (pullback.snd π π) delta h G.s.left := by
      simpa [delta, deltaComp, h, Category.assoc] using hDeltaCompComp.paste_vert hComp
    have hfstEq :
        pullback.fst π π ⁻¹ᵁ V = P.sourceLocus delta := by
      simpa [V] using h_baseChange (f := h) (b := G.t.left)
        (p := pullback.fst π π) (f' := delta) _hQh ht hFstBase
    have hsndEq :
        pullback.snd π π ⁻¹ᵁ V = P.sourceLocus delta := by
      simpa [V] using h_baseChange (f := h) (b := G.s.left)
        (p := pullback.snd π π) (f' := delta) _hQh hs hSndBase
    exact hfstEq.trans hsndEq.symm
  -- Pulling the fiberwise equality back along the section witnesses descent to `U'`.
  let κ : pullback g G.t.left ⟶ pullback π π :=
    pullback.lift (𝟙 (pullback g G.t.left)) (π ≫ σ) (by simp [π, hσ])
  have hκFst : κ ≫ pullback.fst π π = 𝟙 (pullback g G.t.left) := by
    simpa [κ] using
      (pullback.lift_fst (𝟙 (pullback g G.t.left)) (π ≫ σ) (by simp [π, hσ]))
  have hκSnd : κ ≫ pullback.snd π π = π ≫ σ := by
    simpa [κ] using
      (pullback.lift_snd (𝟙 (pullback g G.t.left)) (π ≫ σ) (by simp [π, hσ]))
  have hdescend : V = π ⁻¹ᵁ (σ ⁻¹ᵁ V) := by
    have hpull :
        κ ⁻¹ᵁ (pullback.fst π π ⁻¹ᵁ V) =
          κ ⁻¹ᵁ (pullback.snd π π ⁻¹ᵁ V) := congrArg (fun W ↦ κ ⁻¹ᵁ W) hfiberEq
    calc
      V = (κ ≫ pullback.fst π π) ⁻¹ᵁ V := by
        simpa [hκFst]
      _ = (κ ≫ pullback.snd π π) ⁻¹ᵁ V := by
        simpa [Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj] using hpull
      _ = π ⁻¹ᵁ (σ ⁻¹ᵁ V) := by
        simpa [hκSnd, Scheme.Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
          Category.assoc]
  refine ⟨σ ⁻¹ᵁ V, ?_⟩
  simpa [π, V] using hdescend.symm

end AlgebraicGeometry.GroupoidScheme
