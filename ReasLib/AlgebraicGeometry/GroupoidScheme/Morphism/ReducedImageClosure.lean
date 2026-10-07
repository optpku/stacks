module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.Range
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Subset

/-!
# Composition on reduced image closures of groupoid-scheme morphisms

This module records the restriction of target composition to the reduced closure of an
arrow-map image and its set-theoretic stability over a field-spectrum object scheme.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme.Hom

/-- The target-groupoid composition restricted to the fibre product of the reduced closure of
the arrow-map image with itself. -/
noncomputable def reducedImageClosureComposition {S : Scheme.{u}}
    {G₁ G₂ : GroupoidScheme S} (f : Hom G₁ G₂) :
    Limits.pullback
      (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
      (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) ⟶ G₂.R :=
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  pullback.map (i ≫ G₂.s) (i ≫ G₂.t) G₂.s G₂.t i i (𝟙 G₂.U)
    (Category.comp_id _) (Category.comp_id _) ≫ G₂.c

/-- For an identity-on-objects morphism of groupoid schemes whose object scheme is isomorphic
to the spectrum of a field, target composition on the reduced closure of the arrow-image lands
set-theoretically in that reduced closure. -/
theorem reducedImageClosureComposition_range_subset
    {S : Scheme.{u}} {k : Type u} [Field k] {G₁ G₂ : GroupoidScheme S}
    (eU : Spec (CommRingCat.of k) ≅ G₁.U.left) (hU : G₁.U = G₂.U)
    (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    Set.range (reducedImageClosureComposition f).left ⊆
      Set.range (Scheme.Hom.reducedImageClosureιOver f.arrow).left := by
  let eU₂ : Spec (CommRingCat.of k) ≅ G₂.U.left :=
    eU.trans (eqToIso (congrArg Over.left hU))
  have hObj : f.obj = eqToHom hU := by
    simpa [IsIdentityOnObjects] using hf
  have hObjLeft : f.obj.left = (eqToHom hU).left := by
    exact congrArg Over.Hom.left hObj
  have hMonoObjLeft : Mono f.obj.left := by
    rw [hObjLeft]
    infer_instance
  have hSubsingletonU : Subsingleton G₂.U.left := by
    -- Local instance justification (proof-local temporary data): transfer the canonical
    -- one-point property across the specified object-scheme isomorphism.
    let _ : Subsingleton (Spec (CommRingCat.of k)) := inferInstance
    exact Function.Surjective.subsingleton (Scheme.Hom.surjective eU₂.hom)
  have hIntegralU : AlgebraicGeometry.IsIntegral G₂.U.left :=
    AlgebraicGeometry.IsIntegral.of_isIso eU₂.hom
  have hSchemeComposableRange :
      Set.range
          (pullback.map G₁.s.left G₁.t.left G₂.s.left G₂.t.left
            f.arrow.left f.arrow.left f.obj.left
            (congrArg Over.Hom.left f.map_s) (congrArg Over.Hom.left f.map_t)) =
        Scheme.Pullback.subset G₂.s.left G₂.t.left
          (Set.range f.arrow.left) (Set.range f.arrow.left) := by
    -- Proof comment: on the underlying scheme pullback, `range_map` identifies the image
    -- of the induced map with the pullback subset cut out by the arrow-image.
    simpa [Scheme.Pullback.subset_eq_preimage_inter] using
      (Scheme.Pullback.range_map
        (f := G₁.s.left) (g := G₁.t.left) (f' := G₂.s.left) (g' := G₂.t.left)
        (i₁ := f.arrow.left) (i₂ := f.arrow.left) (i₃ := f.obj.left)
        (e₁ := congrArg Over.Hom.left f.map_s) (e₂ := congrArg Over.Hom.left f.map_t))
  have hSchemeClosureSubset :
      Scheme.Pullback.subset G₂.s.left G₂.t.left
          (closure (Set.range f.arrow.left))
          (closure (Set.range f.arrow.left)) =
        closure
          (Scheme.Pullback.subset G₂.s.left G₂.t.left
            (Set.range f.arrow.left) (Set.range f.arrow.left)) := by
    -- Proof comment: the object scheme is isomorphic to the spectrum of a field, so this
    -- fibre-product closure is the closure of the fibre-product image subset.
    -- Local instance justification (proof-local temporary data): the closure theorem uses
    -- the transferred one-point property only within this proof.
    let _ : Subsingleton G₂.U.left := hSubsingletonU
    -- Local instance justification (proof-local temporary data): the closure theorem uses
    -- the transferred integrality property only within this proof.
    let _ : AlgebraicGeometry.IsIntegral G₂.U.left := hIntegralU
    simpa using
      (Scheme.Pullback.subset_closure_eq_closure_subset
        G₂.s.left G₂.t.left (Set.range f.arrow.left) (Set.range f.arrow.left))
  have hForgetClosureSubset :
      Scheme.Pullback.subset ((Over.forget S).map G₂.s) ((Over.forget S).map G₂.t)
          (closure (Set.range f.arrow.left))
          (closure (Set.range f.arrow.left)) =
        closure
          (Scheme.Pullback.subset ((Over.forget S).map G₂.s) ((Over.forget S).map G₂.t)
            (Set.range f.arrow.left) (Set.range f.arrow.left)) := hSchemeClosureSubset
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  let e :=
    CategoryTheory.Limits.PreservesPullback.iso (CategoryTheory.Over.forget S) G₂.s G₂.t
  let j :
      Limits.pullback (i ≫ G₂.s) (i ≫ G₂.t) ⟶ Limits.pullback G₂.s G₂.t :=
    Limits.pullback.map (i ≫ G₂.s) (i ≫ G₂.t) G₂.s G₂.t i i (𝟙 G₂.U)
      (Category.comp_id _) (Category.comp_id _)
  have hReducedClosureMapsToClosure :
      Set.MapsTo i.left Set.univ (closure (Set.range f.arrow.left)) := by
    intro z hz
    have hz' : i.left z ∈ Set.range i.left := ⟨z, rfl⟩
    rwa [Scheme.Hom.range_reducedImageClosureιOver (f := f.arrow)] at hz'
  have hCompositionMapsToArrowRange :
      Set.MapsTo (e.inv ≫ G₂.c.left)
        (Scheme.Pullback.subset ((Over.forget S).map G₂.s) ((Over.forget S).map G₂.t)
          (Set.range f.arrow.left) (Set.range f.arrow.left))
        (Set.range f.arrow.left) := by
    intro z hz
    rw [Scheme.Pullback.mem_subset_iff] at hz
    let z' : (Limits.pullback G₂.s G₂.t).left := e.inv z
    have hzfst : Over.Hom.left (Limits.pullback.fst G₂.s G₂.t) z' ∈ Set.range f.arrow.left := by
      have hzfst' :=
        congr($(CategoryTheory.Limits.PreservesPullback.iso_inv_fst
          (CategoryTheory.Over.forget S) G₂.s G₂.t) z)
      change Over.Hom.left (Limits.pullback.fst G₂.s G₂.t) z' =
        Limits.pullback.fst G₂.s.left G₂.t.left z at hzfst'
      rw [hzfst']
      exact hz.1
    have hzsnd : Over.Hom.left (Limits.pullback.snd G₂.s G₂.t) z' ∈ Set.range f.arrow.left := by
      have hzsnd' :=
        congr($(CategoryTheory.Limits.PreservesPullback.iso_inv_snd
          (CategoryTheory.Over.forget S) G₂.s G₂.t) z)
      change Over.Hom.left (Limits.pullback.snd G₂.s G₂.t) z' =
        Limits.pullback.snd G₂.s.left G₂.t.left z at hzsnd'
      rw [hzsnd']
      exact hz.2
    -- Proof comment: after transporting the scheme pullback point through the pullback
    -- comparison isomorphism, `rangeArrow_mem_comp` applies directly.
    change G₂.c.left z' ∈ Set.range f.arrow.left
    exact rangeArrow_mem_comp f hf z' hzfst hzsnd
  have hCompositionMapsToClosure :
      Set.MapsTo (e.inv ≫ G₂.c.left)
        (Scheme.Pullback.subset ((Over.forget S).map G₂.s) ((Over.forget S).map G₂.t)
          (closure (Set.range f.arrow.left))
          (closure (Set.range f.arrow.left)))
        (closure (Set.range f.arrow.left)) := by
    -- Proof comment: continuity of composition carries closure-membership on the composable
    -- pair locus to closure-membership in the arrow image.
    have hClosure :=
      hCompositionMapsToArrowRange.closure (e.inv ≫ G₂.c.left).continuous
    rw [← hForgetClosureSubset] at hClosure
    exact hClosure
  rw [Scheme.Hom.range_reducedImageClosureιOver (f := f.arrow)]
  rintro _ ⟨z, rfl⟩
  let y : (Limits.pullback G₂.s G₂.t).left := j.left z
  let w := e.hom y
  have hw :
      w ∈ Scheme.Pullback.subset ((Over.forget S).map G₂.s) ((Over.forget S).map G₂.t)
        (closure (Set.range f.arrow.left))
        (closure (Set.range f.arrow.left)) := by
    rw [Scheme.Pullback.mem_subset_iff]
    constructor
    · -- Proof comment: the first projection is the reduced-closure inclusion applied to the
      -- first source projection, hence it lies in the closure of the original arrow image.
      have hwfstIso :=
        congr($(CategoryTheory.Limits.PreservesPullback.iso_hom_fst
          (CategoryTheory.Over.forget S) G₂.s G₂.t) y)
      change Limits.pullback.fst ((Over.forget S).map G₂.s) ((Over.forget S).map G₂.t) w =
        Over.Hom.left (Limits.pullback.fst G₂.s G₂.t) y at hwfstIso
      have hyfst :
          Over.Hom.left (Limits.pullback.fst G₂.s G₂.t) y =
            i.left (Over.Hom.left (Limits.pullback.fst (i ≫ G₂.s) (i ≫ G₂.t)) z) := by
        have hyfstM :
            j ≫ Limits.pullback.fst G₂.s G₂.t =
              Limits.pullback.fst (i ≫ G₂.s) (i ≫ G₂.t) ≫ i := by
          dsimp [j]
          simpa [Category.assoc] using
            (pullback.lift_fst
              (pullback.fst (i ≫ G₂.s) (i ≫ G₂.t) ≫ i)
              (pullback.snd (i ≫ G₂.s) (i ≫ G₂.t) ≫ i)
              (by
                simpa [Category.assoc] using
                  (pullback.condition_assoc (f := i ≫ G₂.s) (g := i ≫ G₂.t) (h := 𝟙 G₂.U))))
        simpa [y] using
          congrArg
            (fun g : (Limits.pullback (i ≫ G₂.s) (i ≫ G₂.t)).left ⟶ G₂.R.left => g z)
            (congrArg Over.Hom.left hyfstM)
      have hmemFst :
          i.left (Over.Hom.left (Limits.pullback.fst (i ≫ G₂.s) (i ≫ G₂.t)) z) ∈
            closure (Set.range f.arrow.left) := by
        apply hReducedClosureMapsToClosure
        simp
      rw [hwfstIso, hyfst]
      exact hmemFst
    · -- Proof comment: the second projection is handled by the same pullback-map computation.
      have hwsndIso :=
        congr($(CategoryTheory.Limits.PreservesPullback.iso_hom_snd
          (CategoryTheory.Over.forget S) G₂.s G₂.t) y)
      change Limits.pullback.snd ((Over.forget S).map G₂.s) ((Over.forget S).map G₂.t) w =
        Over.Hom.left (Limits.pullback.snd G₂.s G₂.t) y at hwsndIso
      have hysnd :
          Over.Hom.left (Limits.pullback.snd G₂.s G₂.t) y =
            i.left (Over.Hom.left (Limits.pullback.snd (i ≫ G₂.s) (i ≫ G₂.t)) z) := by
        have hysndM :
            j ≫ Limits.pullback.snd G₂.s G₂.t =
              Limits.pullback.snd (i ≫ G₂.s) (i ≫ G₂.t) ≫ i := by
          dsimp [j]
          simpa [Category.assoc] using
            (pullback.lift_snd
              (pullback.fst (i ≫ G₂.s) (i ≫ G₂.t) ≫ i)
              (pullback.snd (i ≫ G₂.s) (i ≫ G₂.t) ≫ i)
              (by
                simpa [Category.assoc] using
                  (pullback.condition_assoc (f := i ≫ G₂.s) (g := i ≫ G₂.t) (h := 𝟙 G₂.U))))
        simpa [y] using
          congrArg
            (fun g : (Limits.pullback (i ≫ G₂.s) (i ≫ G₂.t)).left ⟶ G₂.R.left => g z)
            (congrArg Over.Hom.left hysndM)
      have hmemSnd :
          i.left (Over.Hom.left (Limits.pullback.snd (i ≫ G₂.s) (i ≫ G₂.t)) z) ∈
            closure (Set.range f.arrow.left) := by
        apply hReducedClosureMapsToClosure
        simp
      rw [hwsndIso, hysnd]
      exact hmemSnd
  -- Proof comment: the pullback point lies in the closure subset, so the closure-stable
  -- composition map lands in the closure of the arrow image.
  have hwinv : e.inv w = y := by
    change ((e.hom ≫ e.inv) y) = y
    exact congrArg (fun g ↦ g y) e.hom_inv_id
  have hfinal :
      (e.inv ≫ G₂.c.left) w = (reducedImageClosureComposition f).left z := by
    change G₂.c.left (e.inv w) = (reducedImageClosureComposition f).left z
    rw [hwinv]
    simp [reducedImageClosureComposition, i, j, y]
  rw [← hfinal]
  exact hCompositionMapsToClosure hw

end AlgebraicGeometry.GroupoidScheme.Hom
