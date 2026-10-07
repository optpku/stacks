module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Points

/-!
# Comparison for successive restrictions of a groupoid scheme

This module constructs the canonical comparison morphism for successive restrictions and proves
that both squares in its comparison diagram are pullbacks.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The two original arrows over the middle pullback give a composable pair after inverting
the first arrow. -/
theorem restrictionComparisonComposable {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    (pullback.snd (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.snd (g' ≫ g) G.t) ≫ G.s =
      ((pullback.fst (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.snd g G.t) ≫ G.i) ≫ G.t := by
  let a := pullback.snd g G.t ≫ G.s
  let b := pullback.snd (g' ≫ g) G.t ≫ G.s
  calc
    (pullback.snd a b ≫ pullback.snd (g' ≫ g) G.t) ≫ G.s = pullback.snd a b ≫ b := by
      simp [a, b, Category.assoc]
    _ = pullback.fst a b ≫ a := by
      simpa using (show pullback.fst a b ≫ a = pullback.snd a b ≫ b from pullback.condition).symm
    _ = ((pullback.fst a b ≫ pullback.snd g G.t) ≫ G.i) ≫ G.t := by
      simp [a, Category.assoc, G.inverse_target]

/-- The composite `c(r₁, i(r₀))` has source given by the `U'` component of the middle
pullback. -/
theorem restrictionComparisonPoint_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    G.compose
          (pullback.snd (pullback.snd g G.t ≫ G.s)
              (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
            pullback.snd (g' ≫ g) G.t)
          ((pullback.fst (pullback.snd g G.t ≫ G.s)
              (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
            pullback.snd g G.t) ≫ G.i)
          (restrictionComparisonComposable G g g') ≫ G.s =
      (pullback.fst (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.fst g G.t) ≫ g := by
  let a := pullback.snd g G.t ≫ G.s
  let b := pullback.snd (g' ≫ g) G.t ≫ G.s
  calc
    G.compose
          (pullback.snd a b ≫ pullback.snd (g' ≫ g) G.t)
          ((pullback.fst a b ≫ pullback.snd g G.t) ≫ G.i)
          (restrictionComparisonComposable G g g') ≫ G.s =
      (pullback.fst a b ≫ pullback.snd g G.t) ≫ G.t := by
        simpa [a, b, Category.assoc, G.inverse_source] using
          G.compose_source
            (pullback.snd a b ≫ pullback.snd (g' ≫ g) G.t)
            ((pullback.fst a b ≫ pullback.snd g G.t) ≫ G.i)
            (restrictionComparisonComposable G g g')
    _ = (pullback.fst a b ≫ pullback.fst g G.t) ≫ g := by
      simpa [a, Category.assoc] using
        congrArg (fun k ↦ pullback.fst a b ≫ k)
          ((show pullback.fst g G.t ≫ g = pullback.snd g G.t ≫ G.t from pullback.condition).symm)

/-- The composite `c(r₁, i(r₀))` has target given by the `U''` component followed by
`g' ≫ g`. -/
theorem restrictionComparisonPoint_target {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    G.compose
          (pullback.snd (pullback.snd g G.t ≫ G.s)
              (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
            pullback.snd (g' ≫ g) G.t)
          ((pullback.fst (pullback.snd g G.t ≫ G.s)
              (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
            pullback.snd g G.t) ≫ G.i)
          (restrictionComparisonComposable G g g') ≫ G.t =
      ((pullback.snd (pullback.snd g G.t ≫ G.s)
            (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
          pullback.fst (g' ≫ g) G.t) ≫ g') ≫ g := by
  let a := pullback.snd g G.t ≫ G.s
  let b := pullback.snd (g' ≫ g) G.t ≫ G.s
  calc
    G.compose
          (pullback.snd a b ≫ pullback.snd (g' ≫ g) G.t)
          ((pullback.fst a b ≫ pullback.snd g G.t) ≫ G.i)
          (restrictionComparisonComposable G g g') ≫ G.t =
      (pullback.snd a b ≫ pullback.snd (g' ≫ g) G.t) ≫ G.t := by
        simpa [a, b, Category.assoc] using
          G.compose_target
            (pullback.snd a b ≫ pullback.snd (g' ≫ g) G.t)
            ((pullback.fst a b ≫ pullback.snd g G.t) ≫ G.i)
            (restrictionComparisonComposable G g g')
    _ = ((pullback.snd a b ≫ pullback.fst (g' ≫ g) G.t) ≫ g') ≫ g := by
      simpa [b, Category.assoc] using
        congrArg (fun k ↦ pullback.snd a b ≫ k)
          (show pullback.fst (g' ≫ g) G.t ≫ (g' ≫ g) =
              pullback.snd (g' ≫ g) G.t ≫ G.t from pullback.condition).symm

/-- The pointwise arrow `c(r₁, i(r₀))` between the two objects lying over `U'`. -/
def restrictionComparisonPoint {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    G.PointHom
      ((pullback.fst (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.fst g G.t) ≫ g)
      (((pullback.snd (pullback.snd g G.t ≫ G.s)
            (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
          pullback.fst (g' ≫ g) G.t) ≫ g') ≫ g) :=
  PointHom.ofArrow
    (G.compose
      (pullback.snd (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.snd (g' ≫ g) G.t)
      ((pullback.fst (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.snd g G.t) ≫ G.i)
      (restrictionComparisonComposable G g g'))
    (restrictionComparisonPoint_source G g g')
    (restrictionComparisonPoint_target G g g')

/-- The comparison morphism for two successive restrictions of a groupoid scheme. -/
def restrictionComparison {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    Limits.pullback (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s) ⟶
      Limits.pullback g' (G.toPreRelation.pullback g).t :=
  pullback.lift
    (pullback.snd (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
      pullback.fst (g' ≫ g) G.t)
    (G.liftPoint g (restrictionComparisonPoint G g g')).arrow
    (by
      simpa [AlgebraicGeometry.GroupoidScheme.pullback] using
        ((G.liftPoint g (restrictionComparisonPoint G g g')).target).symm)

/-- The first projection of `restrictionComparison` is the `U''` projection. -/
theorem restrictionComparison_fst {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    restrictionComparison G g g' ≫
        pullback.fst g' (G.toPreRelation.pullback g).t =
      pullback.snd (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.fst (g' ≫ g) G.t := by
  unfold restrictionComparison
  exact pullback.lift_fst _ _ _

/-- The second projection of `restrictionComparison` is the constructed restricted arrow. -/
theorem restrictionComparison_snd {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    restrictionComparison G g g' ≫
        pullback.snd g' (G.toPreRelation.pullback g).t =
      (G.liftPoint g (restrictionComparisonPoint G g g')).arrow := by
  unfold restrictionComparison
  exact pullback.lift_snd _ _ _

/-- Forgetting a lifted restricted point recovers the original arrow in `G.R`. -/
theorem liftPointArrowImage {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) {T : Over S} {x y : T ⟶ U'}
    (p : G.PointHom (x ≫ g) (y ≫ g)) :
    (G.liftPoint g p).arrow ≫ pullbackArrow G g = p.arrow := by
  -- Compare the arrow map on points with the explicit restriction comparison.
  have hArrow :
      (((pullbackHom G g).mapPoints.app (Opposite.op T)).map (G.liftPoint g p)).arrow =
        (G.liftPoint g p).arrow ≫ pullbackArrow G g :=
    (pullbackHom G g).mapPoints_app_map_arrow (Opposite.op T) (G.liftPoint g p)
  have hMap :
      (((pullbackHom G g).mapPoints.app (Opposite.op T)).map (G.liftPoint g p)).arrow =
        p.arrow :=
    map_liftPoint_arrow G g p
  calc
    (G.liftPoint g p).arrow ≫ pullbackArrow G g =
        (((pullbackHom G g).mapPoints.app (Opposite.op T)).map (G.liftPoint g p)).arrow := by
          symm
          exact hArrow
    _ = p.arrow := hMap

/-- The comparison morphism lies over the source map of the first restriction. -/
theorem restrictionComparison_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    restrictionComparison G g g' ≫
        pullback.snd g' (G.toPreRelation.pullback g).t ≫
        (G.toPreRelation.pullback g).s =
      pullback.fst (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.fst g G.t := by
  -- Read the source of the lifted restricted arrow constructed by `restrictionComparison`.
  have hSourceLift :
      restrictionComparison G g g' ≫
          pullback.snd g' (G.toPreRelation.pullback g).t =
        (G.liftPoint g (restrictionComparisonPoint G g g')).arrow :=
    restrictionComparison_snd G g g'
  change
      (restrictionComparison G g g' ≫
          pullback.snd g' (G.toPreRelation.pullback g).t) ≫
        (G.toPreRelation.pullback g).s =
      pullback.fst (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.fst g G.t
  rw [hSourceLift]
  simpa [AlgebraicGeometry.GroupoidScheme.pullback, Category.assoc] using
    (G.liftPoint g (restrictionComparisonPoint G g g')).source

/-- The restricted comparison arrow has target equal to the second middle projection followed
by the morphism defining the second restriction. -/
theorem restrictionComparison_target {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    restrictionComparison G g g' ≫
        pullback.snd g' (G.toPreRelation.pullback g).t ≫
        (G.toPreRelation.pullback g).t =
      pullback.snd (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.fst (g' ≫ g) G.t ≫ g' := by
  have hTargetLift :
      restrictionComparison G g g' ≫
          pullback.snd g' (G.toPreRelation.pullback g).t =
        (G.liftPoint g (restrictionComparisonPoint G g g')).arrow :=
    restrictionComparison_snd G g g'
  change
      (restrictionComparison G g g' ≫
          pullback.snd g' (G.toPreRelation.pullback g).t) ≫
        (G.toPreRelation.pullback g).t =
      pullback.snd (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.fst (g' ≫ g) G.t ≫ g'
  rw [hTargetLift]
  simpa [AlgebraicGeometry.GroupoidScheme.pullback, Category.assoc] using
    (G.liftPoint g (restrictionComparisonPoint G g g')).target

/-- Forgetting the restricted comparison arrow recovers the explicit composite in `G.R`. -/
theorem restrictionComparison_arrowImage {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    restrictionComparison G g g' ≫
        pullback.snd g' (G.toPreRelation.pullback g).t ≫
        pullbackArrow G g =
      G.compose
        (pullback.snd (pullback.snd g G.t ≫ G.s)
            (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
          pullback.snd (g' ≫ g) G.t)
        ((pullback.fst (pullback.snd g G.t ≫ G.s)
            (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
          pullback.snd g G.t) ≫
          G.i)
        (restrictionComparisonComposable G g g') := by
  -- Forgetting the lifted point identifies the restricted arrow with its original arrow.
  have hSourceLift :
      restrictionComparison G g g' ≫
          pullback.snd g' (G.toPreRelation.pullback g).t =
        (G.liftPoint g (restrictionComparisonPoint G g g')).arrow :=
    restrictionComparison_snd G g g'
  change
      (restrictionComparison G g g' ≫
          pullback.snd g' (G.toPreRelation.pullback g).t) ≫
        pullbackArrow G g =
      G.compose
        (pullback.snd (pullback.snd g G.t ≫ G.s)
            (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
          pullback.snd (g' ≫ g) G.t)
        ((pullback.fst (pullback.snd g G.t ≫ G.s)
            (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
          pullback.snd g G.t) ≫
          G.i)
        (restrictionComparisonComposable G g g')
  rw [hSourceLift]
  calc
    (G.liftPoint g (restrictionComparisonPoint G g g')).arrow ≫ pullbackArrow G g =
        (restrictionComparisonPoint G g g').arrow := by
          simpa using
            liftPointArrowImage G g (restrictionComparisonPoint G g g')
    _ =
        G.compose
          (pullback.snd (pullback.snd g G.t ≫ G.s)
              (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
            pullback.snd (g' ≫ g) G.t)
          ((pullback.fst (pullback.snd g G.t ≫ G.s)
              (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
            pullback.snd g G.t) ≫
            G.i)
          (restrictionComparisonComposable G g g') := by
          simpa [restrictionComparisonPoint] using
            (PointHom.ofArrow_arrow
              (G.compose
                (pullback.snd (pullback.snd g G.t ≫ G.s)
                    (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                  pullback.snd (g' ≫ g) G.t)
                ((pullback.fst (pullback.snd g G.t ≫ G.s)
                    (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                  pullback.snd g G.t) ≫
                  G.i)
                (restrictionComparisonComposable G g g'))
              (restrictionComparisonPoint_source G g g')
              (restrictionComparisonPoint_target G g g'))

/-- Composing `c(r₁, i(r₀))` with `r₀` recovers `r₁` once the composability data is fixed. -/
theorem recomposeComparisonArrow {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (r₀ r₁ : T ⟶ G.R)
    (hInv : r₁ ≫ G.s = (r₀ ≫ G.i) ≫ G.t)
    (hInvComp : (r₀ ≫ G.i) ≫ G.s = r₀ ≫ G.t)
    (hRightAssoc : G.compose r₁ (r₀ ≫ G.i) hInv ≫ G.s = r₀ ≫ G.t) :
    G.compose (G.compose r₁ (r₀ ≫ G.i) hInv) r₀ hRightAssoc = r₁ := by
  -- First reassociate so that the inverse pair is composed together.
  have hComposeInverse :
      G.compose (r₀ ≫ G.i) r₀ hInvComp = (r₀ ≫ G.s) ≫ G.e := by
    simpa [Category.assoc] using G.inverse_compose r₀ hInvComp
  have hAssocRight :
      r₁ ≫ G.s = G.compose (r₀ ≫ G.i) r₀ hInvComp ≫ G.t := by
    calc
      r₁ ≫ G.s = (r₀ ≫ G.i) ≫ G.t := hInv
      _ = G.compose (r₀ ≫ G.i) r₀ hInvComp ≫ G.t := by
        symm
        simpa [Category.assoc] using G.compose_target (r₀ ≫ G.i) r₀ hInvComp
  calc
    G.compose (G.compose r₁ (r₀ ≫ G.i) hInv) r₀ hRightAssoc =
        G.compose r₁ (G.compose (r₀ ≫ G.i) r₀ hInvComp) hAssocRight := by
          simpa using
            G.compose_assoc r₁ (r₀ ≫ G.i) r₀ hInv hInvComp hRightAssoc hAssocRight
    _ = r₁ := by
        have hComposeInverse' :
            G.compose (r₀ ≫ G.i) r₀ hInvComp = (r₁ ≫ G.s) ≫ G.e := by
          calc
            G.compose (r₀ ≫ G.i) r₀ hInvComp = (r₀ ≫ G.s) ≫ G.e := hComposeInverse
            _ = ((r₀ ≫ G.i) ≫ G.t) ≫ G.e := by
              simp [Category.assoc, G.inverse_target]
            _ = (r₁ ≫ G.s) ≫ G.e := by
              rw [hInv.symm]
        have hRightIdentity :
            r₁ ≫ G.s = ((r₁ ≫ G.s) ≫ G.e) ≫ G.t := by
          simp [Category.assoc, G.identity_target]
        simpa [hComposeInverse'] using G.compose_right_identity r₁ hRightIdentity

/-- Composing `c(r₁, r₀)` with the inverse of `r₀` recovers `r₁`. -/
theorem compose_cancel_right_inverse {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (r₁ r₀ : T ⟶ G.R)
    (h : r₁ ≫ G.s = r₀ ≫ G.t)
    (h' : G.compose r₁ r₀ h ≫ G.s = (r₀ ≫ G.i) ≫ G.t) :
    G.compose (G.compose r₁ r₀ h) (r₀ ≫ G.i) h' = r₁ := by
  -- Reassociate so the inverse pair `r₀ ⋅ i(r₀)` is composed first.
  have hInv : r₀ ≫ G.s = (r₀ ≫ G.i) ≫ G.t := by
    simp [Category.assoc, G.inverse_target]
  have hAssoc :
      r₁ ≫ G.s = G.compose r₀ (r₀ ≫ G.i) hInv ≫ G.t := by
    calc
      r₁ ≫ G.s = r₀ ≫ G.t := h
      _ = G.compose r₀ (r₀ ≫ G.i) hInv ≫ G.t := by
        symm
        simpa [Category.assoc] using G.compose_target r₀ (r₀ ≫ G.i) hInv
  calc
    G.compose (G.compose r₁ r₀ h) (r₀ ≫ G.i) h' =
        G.compose r₁ (G.compose r₀ (r₀ ≫ G.i) hInv) hAssoc := by
          simpa using G.compose_assoc r₁ r₀ (r₀ ≫ G.i) h hInv h' hAssoc
    _ = r₁ := by
        have hComposeInverse :
            G.compose r₀ (r₀ ≫ G.i) hInv = (r₀ ≫ G.t) ≫ G.e := by
          simpa using G.compose_inverse r₀ hInv
        have hComposeInverse' :
            G.compose r₀ (r₀ ≫ G.i) hInv = (r₁ ≫ G.s) ≫ G.e := by
          calc
            G.compose r₀ (r₀ ≫ G.i) hInv = (r₀ ≫ G.t) ≫ G.e := hComposeInverse
            _ = (r₁ ≫ G.s) ≫ G.e := by rw [h.symm]
        have hRightIdentity :
            r₁ ≫ G.s = ((r₁ ≫ G.s) ≫ G.e) ≫ G.t := by
          simp [Category.assoc, G.identity_target]
        simpa [hComposeInverse'] using G.compose_right_identity r₁ hRightIdentity

/-- Precomposing a pointwise groupoid composite agrees with composing the precomposed arrows. -/
theorem comp_compose {S : Scheme.{u}} (G : GroupoidScheme S) {T T' : Over S}
    (m : T' ⟶ T) (a b : T ⟶ G.R)
    (h : a ≫ G.s = b ≫ G.t)
    (h' : (m ≫ a) ≫ G.s = (m ≫ b) ≫ G.t) :
    m ≫ G.compose a b h = G.compose (m ≫ a) (m ≫ b) h' := by
  -- Compare the two lifts into the composability pullback before composing with `G.c`.
  unfold GroupoidScheme.compose
  have hLift :
      m ≫ pullback.lift a b h = pullback.lift (m ≫ a) (m ≫ b) h' := by
    apply pullback.hom_ext
    · calc
        m ≫ pullback.lift a b h ≫ pullback.fst G.s G.t = m ≫ a := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ m ≫ k) (pullback.lift_fst a b h)
        _ = pullback.lift (m ≫ a) (m ≫ b) h' ≫ pullback.fst G.s G.t := by
          symm
          exact pullback.lift_fst (m ≫ a) (m ≫ b) h'
    · calc
        m ≫ pullback.lift a b h ≫ pullback.snd G.s G.t = m ≫ b := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ m ≫ k) (pullback.lift_snd a b h)
        _ = pullback.lift (m ≫ a) (m ≫ b) h' ≫ pullback.snd G.s G.t := by
          symm
          exact pullback.lift_snd (m ≫ a) (m ≫ b) h'
  simpa [Category.assoc] using congrArg (fun k ↦ k ≫ G.c) hLift

/-- The reconstructed arrow has source equal to the source of the left-hand arrow. -/
theorem restrictionComparisonCompositeSource {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U')
    {T : Over S}
    (α : T ⟶ Limits.pullback g G.t)
    (β : T ⟶ Limits.pullback g' (G.toPreRelation.pullback g).t)
    (hcomp :
      (β ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g) ≫ G.s =
        (α ≫ pullback.snd g G.t) ≫ G.t) :
    G.compose
        (β ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g)
        (α ≫ pullback.snd g G.t)
        hcomp ≫
        G.s =
      α ≫ pullback.snd g G.t ≫ G.s := by
  -- The source of a pointwise composite is the source of its second factor.
  simpa [Category.assoc] using
    G.compose_source
      (β ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g)
      (α ≫ pullback.snd g G.t)
      hcomp

/-- The reconstructed arrow has target equal to the `U''` component followed by `g' ≫ g`. -/
theorem restrictionComparisonCompositeTarget {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U')
    {T : Over S}
    (α : T ⟶ Limits.pullback g G.t)
    (β : T ⟶ Limits.pullback g' (G.toPreRelation.pullback g).t)
    (hcomp :
      (β ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g) ≫ G.s =
        (α ≫ pullback.snd g G.t) ≫ G.t) :
    G.compose
        (β ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g)
        (α ≫ pullback.snd g G.t)
        hcomp ≫
        G.t =
      ((β ≫ pullback.fst g' (G.toPreRelation.pullback g).t) ≫ g') ≫ g := by
  -- Rewrite the target through the forgotten restricted arrow and the pullback conditions.
  calc
    G.compose
        (β ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g)
        (α ≫ pullback.snd g G.t)
        hcomp ≫
        G.t =
      (β ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g) ≫ G.t := by
          simpa [Category.assoc] using
            G.compose_target
              (β ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g)
              (α ≫ pullback.snd g G.t)
              hcomp
    _ = β ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫
          (G.toPreRelation.pullback g).t ≫ g := by
          simp [Category.assoc, pullbackArrow_t]
    _ = ((β ≫ pullback.fst g' (G.toPreRelation.pullback g).t) ≫ g') ≫ g := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ β ≫ k ≫ g)
              (show
                pullback.fst g' (G.toPreRelation.pullback g).t ≫ g' =
                  pullback.snd g' (G.toPreRelation.pullback g).t ≫
                    (G.toPreRelation.pullback g).t by
                  exact pullback.condition).symm

/-- A morphism into the restricted arrow scheme is determined by its two endpoints and its
image in the original arrow scheme. -/
theorem pullbackArrow_ext {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) {T : Over S} {u v : T ⟶ (G.toPreRelation.pullback g).left}
    (hSource : u ≫ (G.toPreRelation.pullback g).s = v ≫ (G.toPreRelation.pullback g).s)
    (hTarget : u ≫ (G.toPreRelation.pullback g).t = v ≫ (G.toPreRelation.pullback g).t)
    (hArrow : u ≫ pullbackArrow G g = v ≫ pullbackArrow G g) :
    u = v := by
  -- Compare the two maps in the defining pullback presentation of the restricted arrow scheme.
  apply pullback.hom_ext
  · change u ≫ pullbackArrow G g = v ≫ pullbackArrow G g
    exact hArrow
  · change u ≫ (G.toPreRelation.pullback g).hom = v ≫ (G.toPreRelation.pullback g).hom
    rw [AlgebraicGeometry.Scheme.PreRelation.hom_eq_prod_lift]
    -- Equality in the product is controlled by the target and source projections.
    apply prod.hom_ext
    · simpa [AlgebraicGeometry.Scheme.PreRelation.t, Category.assoc, Limits.prod.lift_fst] using
        hTarget
    · simpa [AlgebraicGeometry.Scheme.PreRelation.s, Category.assoc, Limits.prod.lift_snd] using
        hSource

/-- A morphism into the pullback defining the restricted target is determined by its `U''`
projection, its restricted source, and its forgotten arrow in `G.R`. -/
theorem restrictedTargetPullback_ext {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') {T : Over S}
    {u v : T ⟶ Limits.pullback g' (G.toPreRelation.pullback g).t}
    (hFst :
      u ≫ pullback.fst g' (G.toPreRelation.pullback g).t =
        v ≫ pullback.fst g' (G.toPreRelation.pullback g).t)
    (hSource :
      u ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫
          (G.toPreRelation.pullback g).s =
        v ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫
          (G.toPreRelation.pullback g).s)
    (hArrow :
      u ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g =
        v ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g) :
    u = v := by
  apply pullback.hom_ext
  · exact hFst
  · -- The second components agree once their target projections and forgotten arrows agree.
    refine (pullbackArrow_ext (G := G) (g := g)
      (u := u ≫ pullback.snd g' (G.toPreRelation.pullback g).t)
      (v := v ≫ pullback.snd g' (G.toPreRelation.pullback g).t)
      ?_ ?_ ?_)
    · exact hSource
    · have hCondition :
          pullback.fst g' (G.toPreRelation.pullback g).t ≫ g' =
            pullback.snd g' (G.toPreRelation.pullback g).t ≫
              (G.toPreRelation.pullback g).t :=
        pullback.condition
      calc
        u ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫
            (G.toPreRelation.pullback g).t =
          u ≫ pullback.fst g' (G.toPreRelation.pullback g).t ≫ g' := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ u ≫ k) hCondition.symm
        _ = v ≫ pullback.fst g' (G.toPreRelation.pullback g).t ≫ g' := by
            simpa [Category.assoc] using congrArg (fun k ↦ k ≫ g') hFst
        _ = v ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫
              (G.toPreRelation.pullback g).t := by
            simpa [Category.assoc] using congrArg (fun k ↦ v ≫ k) hCondition
    · simpa [Category.assoc] using hArrow

/-- A map into the middle pullback is determined by its left boundary and its image under the
comparison morphism. -/
theorem restrictionComparisonMiddle_snd_eq_of_boundary_eq {S : Scheme.{u}}
    (G : GroupoidScheme S) {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U')
    {T : Over S}
    {φ φ' : T ⟶ Limits.pullback (pullback.snd g G.t ≫ G.s)
      (pullback.snd (g' ≫ g) G.t ≫ G.s)}
    (hTop : φ ≫ restrictionComparison G g g' = φ' ≫ restrictionComparison G g g')
    (hLeft :
      φ ≫ pullback.fst (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) =
        φ' ≫ pullback.fst (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s)) :
    φ ≫ pullback.snd (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s) =
      φ' ≫ pullback.snd (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s) := by
  -- The inner pullback map is determined by its `U''`-projection and its arrow component.
  apply pullback.hom_ext
  · simpa [Category.assoc, restrictionComparison_fst] using
      congrArg
        (fun k ↦ k ≫ pullback.fst g' (G.toPreRelation.pullback g).t)
        hTop
  · -- Recover each middle arrow from its comparison image and the common left boundary.
    let middleArrow :
        Limits.pullback (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ⟶ G.R :=
      pullback.snd (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.snd (g' ≫ g) G.t
    let leftArrow :
        Limits.pullback (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ⟶ G.R :=
      pullback.fst (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
        pullback.snd g G.t
    let comparisonImage :
        Limits.pullback (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ⟶ G.R :=
      restrictionComparison G g g' ≫
        pullback.snd g' (G.toPreRelation.pullback g).t ≫
        pullbackArrow G g
    let r₀ : T ⟶ G.R := φ ≫ leftArrow
    let r₀' : T ⟶ G.R := φ' ≫ leftArrow
    let r : T ⟶ G.R := φ ≫ comparisonImage
    let r' : T ⟶ G.R := φ' ≫ comparisonImage
    let q : T ⟶ G.R := φ ≫ middleArrow
    let q' : T ⟶ G.R := φ' ≫ middleArrow
    have hLeftArrow : r₀ = r₀' := by
      simpa [r₀, r₀', leftArrow, Category.assoc] using
        congrArg (fun k ↦ k ≫ pullback.snd g G.t) hLeft
    have hImage : r = r' := by
      simpa [r, r', comparisonImage, Category.assoc] using
        congrArg
          (fun k ↦ k ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g)
          hTop
    have hInv :
        q ≫ G.s = (r₀ ≫ G.i) ≫ G.t := by
      simpa [q, r₀, middleArrow, leftArrow, Category.assoc] using
        congrArg (fun k ↦ φ ≫ k) (restrictionComparisonComposable G g g')
    have hInv' :
        q' ≫ G.s = (r₀' ≫ G.i) ≫ G.t := by
      simpa [q', r₀', middleArrow, leftArrow, Category.assoc] using
        congrArg (fun k ↦ φ' ≫ k) (restrictionComparisonComposable G g g')
    have hFormula :
        r = G.compose q (r₀ ≫ G.i) hInv := by
      calc
        r = φ ≫
            G.compose middleArrow (leftArrow ≫ G.i)
              (restrictionComparisonComposable G g g') := by
                simpa [r, comparisonImage, middleArrow, leftArrow, Category.assoc] using
                  congrArg (fun k ↦ φ ≫ k) (restrictionComparison_arrowImage G g g')
        _ = G.compose q (r₀ ≫ G.i) hInv := by
            simpa [q, r₀, middleArrow, leftArrow, Category.assoc] using
              comp_compose G φ middleArrow (leftArrow ≫ G.i)
                (restrictionComparisonComposable G g g') hInv
    have hFormula' :
        r' = G.compose q' (r₀' ≫ G.i) hInv' := by
      calc
        r' = φ' ≫
            G.compose middleArrow (leftArrow ≫ G.i)
              (restrictionComparisonComposable G g g') := by
                simpa [r', comparisonImage, middleArrow, leftArrow, Category.assoc] using
                  congrArg (fun k ↦ φ' ≫ k) (restrictionComparison_arrowImage G g g')
        _ = G.compose q' (r₀' ≫ G.i) hInv' := by
            simpa [q', r₀', middleArrow, leftArrow, Category.assoc] using
              comp_compose G φ' middleArrow (leftArrow ≫ G.i)
                (restrictionComparisonComposable G g g') hInv'
    have hRightAssoc :
        r ≫ G.s = r₀ ≫ G.t := by
      calc
        r ≫ G.s = G.compose q (r₀ ≫ G.i) hInv ≫ G.s := by rw [hFormula]
        _ = (r₀ ≫ G.i) ≫ G.s := by
          simpa [Category.assoc] using G.compose_source q (r₀ ≫ G.i) hInv
        _ = r₀ ≫ G.t := by
          simp [Category.assoc, G.inverse_source]
    have hRightAssoc' :
        r' ≫ G.s = r₀' ≫ G.t := by
      calc
        r' ≫ G.s = G.compose q' (r₀' ≫ G.i) hInv' ≫ G.s := by rw [hFormula']
        _ = (r₀' ≫ G.i) ≫ G.s := by
          simpa [Category.assoc] using G.compose_source q' (r₀' ≫ G.i) hInv'
        _ = r₀' ≫ G.t := by
          simp [Category.assoc, G.inverse_source]
    have hRightAssocFormula :
        G.compose q (r₀ ≫ G.i) hInv ≫ G.s = r₀ ≫ G.t := by
      calc
        G.compose q (r₀ ≫ G.i) hInv ≫ G.s = r ≫ G.s := by rw [← hFormula]
        _ = r₀ ≫ G.t := hRightAssoc
    have hRightAssocFormula' :
        G.compose q' (r₀' ≫ G.i) hInv' ≫ G.s = r₀' ≫ G.t := by
      calc
        G.compose q' (r₀' ≫ G.i) hInv' ≫ G.s = r' ≫ G.s := by rw [← hFormula']
        _ = r₀' ≫ G.t := hRightAssoc'
    have hRecover :
        G.compose r r₀ hRightAssoc = q := by
      have hInvComp : (r₀ ≫ G.i) ≫ G.s = r₀ ≫ G.t := by
        simp [Category.assoc, G.inverse_source]
      have hRecoverFormula :
          G.compose (G.compose q (r₀ ≫ G.i) hInv) r₀ hRightAssocFormula = q := by
        simpa [q, r₀, Category.assoc] using
          recomposeComparisonArrow G r₀ q hInv hInvComp hRightAssocFormula
      simpa [hFormula] using hRecoverFormula
    have hRecover' :
        G.compose r' r₀' hRightAssoc' = q' := by
      have hInvComp' : (r₀' ≫ G.i) ≫ G.s = r₀' ≫ G.t := by
        simp [Category.assoc, G.inverse_source]
      have hRecoverFormula' :
          G.compose (G.compose q' (r₀' ≫ G.i) hInv') r₀' hRightAssocFormula' = q' := by
        simpa [q', r₀', Category.assoc] using
          recomposeComparisonArrow G r₀' q' hInv' hInvComp' hRightAssocFormula'
      simpa [hFormula'] using hRecoverFormula'
    calc
      φ ≫ pullback.snd (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
          pullback.snd (g' ≫ g) G.t = q := by
            rfl
      _ = G.compose r r₀ hRightAssoc := by
            symm
            exact hRecover
      _ = G.compose r' r₀' hRightAssoc' := by
            simp [hImage, hLeftArrow]
      _ = q' := hRecover'
      _ = φ' ≫ pullback.snd (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
          pullback.snd (g' ≫ g) G.t := by
            rfl

/-- For two successive restrictions of a groupoid scheme, the square formed by the comparison
morphism, the first middle projection, the restricted source map, and the first projection of
the original restriction is cartesian. -/
theorem restrictionComparisonLeftIsPullback {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    IsPullback (restrictionComparison G g g')
      (pullback.fst (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s))
      (pullback.snd g' (G.pullback g).t ≫ (G.pullback g).s)
      (pullback.fst g G.t) := by
  refine CategoryTheory.IsPullback.mk' ?_ ?_ ?_
  · -- The comparison morphism lands over the restricted source map.
    simpa [AlgebraicGeometry.GroupoidScheme.pullback, Category.assoc] using
      (restrictionComparison_source G g g')
  · intro T φ φ' hTop hLeft
    -- The middle pullback is determined by its left boundary and its comparison image.
    apply pullback.hom_ext
    · exact hLeft
    · exact restrictionComparisonMiddle_snd_eq_of_boundary_eq G g g' hTop hLeft
  · intro T α β hBoundary
    -- Rewrite the boundary through the explicit presentation of the restricted groupoid.
    have hBoundary' :
        α ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫
            (G.toPreRelation.pullback g).s =
          β ≫ pullback.fst g G.t := by
      simpa [AlgebraicGeometry.GroupoidScheme.pullback, Category.assoc] using hBoundary
    -- The forgotten restricted arrow from `α` composes with the arrow from `β`.
    have hcomp :
        (α ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g) ≫ G.s =
          (β ≫ pullback.snd g G.t) ≫ G.t := by
      calc
        (α ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g) ≫ G.s =
            α ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫
              (G.toPreRelation.pullback g).s ≫ g := by
                simp [Category.assoc, pullbackArrow_s]
        _ = β ≫ pullback.fst g G.t ≫ g := by
              simpa [Category.assoc] using congrArg (fun k ↦ k ≫ g) hBoundary'
        _ = (β ≫ pullback.snd g G.t) ≫ G.t := by
              simpa [Category.assoc] using
                congrArg (fun k ↦ β ≫ k)
                  (show pullback.fst g G.t ≫ g = pullback.snd g G.t ≫ G.t from
                    pullback.condition)
    let q : T ⟶ G.R :=
      G.compose
        (α ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g)
        (β ≫ pullback.snd g G.t)
        hcomp
    -- Package the composite arrow into the pullback over `g' ≫ g`.
    have hqSource :
        q ≫ G.s = β ≫ pullback.snd g G.t ≫ G.s := by
      simpa [q] using restrictionComparisonCompositeSource G g g' β α hcomp
    have hqTarget :
        q ≫ G.t =
          ((α ≫ pullback.fst g' (G.toPreRelation.pullback g).t) ≫ g') ≫ g := by
      simpa [q] using restrictionComparisonCompositeTarget G g g' β α hcomp
    let γ : T ⟶ Limits.pullback (g' ≫ g) G.t :=
      pullback.lift
        (α ≫ pullback.fst g' (G.toPreRelation.pullback g).t)
        q
        (by simpa [Category.assoc] using hqTarget.symm)
    have hγ_fst :
        γ ≫ pullback.fst (g' ≫ g) G.t =
          α ≫ pullback.fst g' (G.toPreRelation.pullback g).t := by
      exact pullback.lift_fst _ _ _
    have hγ_snd : γ ≫ pullback.snd (g' ≫ g) G.t = q := by
      exact pullback.lift_snd _ _ _
    have hMiddle :
        β ≫ pullback.snd g G.t ≫ G.s =
          γ ≫ pullback.snd (g' ≫ g) G.t ≫ G.s := by
      calc
        β ≫ pullback.snd g G.t ≫ G.s = q ≫ G.s := by
          simpa [Category.assoc] using hqSource.symm
        _ = γ ≫ pullback.snd (g' ≫ g) G.t ≫ G.s := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ G.s) hγ_snd.symm
    let candidate :
        T ⟶ Limits.pullback (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) :=
      pullback.lift β γ hMiddle
    have hCandidate_fst :
        candidate ≫ pullback.fst (pullback.snd g G.t ≫ G.s)
            (pullback.snd (g' ≫ g) G.t ≫ G.s) =
          β := by
      exact pullback.lift_fst _ _ _
    have hCandidate_snd :
        candidate ≫ pullback.snd (pullback.snd g G.t ≫ G.s)
            (pullback.snd (g' ≫ g) G.t ≫ G.s) =
          γ := by
      exact pullback.lift_snd _ _ _
    have hCancel :
        q ≫ G.s = ((β ≫ pullback.snd g G.t) ≫ G.i) ≫ G.t := by
      calc
        q ≫ G.s = β ≫ pullback.snd g G.t ≫ G.s := hqSource
        _ = ((β ≫ pullback.snd g G.t) ≫ G.i) ≫ G.t := by
              simp [Category.assoc, G.inverse_target]
    have hCandidateTop : candidate ≫ restrictionComparison G g g' = α := by
      apply restrictedTargetPullback_ext (G := G) (g := g) (g' := g')
      · -- The candidate keeps the `U''`-component coming from `α`.
        calc
          candidate ≫ restrictionComparison G g g' ≫
              pullback.fst g' (G.toPreRelation.pullback g).t =
            candidate ≫
              pullback.snd (pullback.snd g G.t ≫ G.s)
                (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
              pullback.fst (g' ≫ g) G.t := by
                rw [restrictionComparison_fst]
          _ = γ ≫ pullback.fst (g' ≫ g) G.t := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ k ≫ pullback.fst (g' ≫ g) G.t) hCandidate_snd
          _ = α ≫ pullback.fst g' (G.toPreRelation.pullback g).t := hγ_fst
      · -- The boundary condition matches the restricted source component.
        calc
          candidate ≫ restrictionComparison G g g' ≫
              pullback.snd g' (G.toPreRelation.pullback g).t ≫
              (G.toPreRelation.pullback g).s =
            candidate ≫
              pullback.fst (pullback.snd g G.t ≫ G.s)
                (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
              pullback.fst g G.t := by
                rw [restrictionComparison_source]
          _ = β ≫ pullback.fst g G.t := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ k ≫ pullback.fst g G.t) hCandidate_fst
          _ = α ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫
                (G.toPreRelation.pullback g).s := by
                simpa [Category.assoc] using hBoundary'.symm
      · -- Route correction: finish in `G.R` by cancelling the right inverse, not by more
        -- pullback transport.
        have hCandidateMiddle :
            candidate ≫
                pullback.snd (pullback.snd g G.t ≫ G.s)
                  (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                pullback.snd (g' ≫ g) G.t =
              q := by
          calc
            candidate ≫
                pullback.snd (pullback.snd g G.t ≫ G.s)
                  (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                pullback.snd (g' ≫ g) G.t =
              γ ≫ pullback.snd (g' ≫ g) G.t := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ k ≫ pullback.snd (g' ≫ g) G.t) hCandidate_snd
            _ = q := hγ_snd
        have hCandidateLeftInv :
            candidate ≫
                ((pullback.fst (pullback.snd g G.t ≫ G.s)
                    (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                  pullback.snd g G.t) ≫
                  G.i) =
              ((β ≫ pullback.snd g G.t) ≫ G.i) := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ pullback.snd g G.t ≫ G.i) hCandidate_fst
        have hOuterComp :
            (candidate ≫
                pullback.snd (pullback.snd g G.t ≫ G.s)
                  (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                pullback.snd (g' ≫ g) G.t) ≫
                G.s =
              (candidate ≫
                  ((pullback.fst (pullback.snd g G.t ≫ G.s)
                      (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                    pullback.snd g G.t) ≫
                    G.i)) ≫
                G.t := by
          calc
            (candidate ≫
                pullback.snd (pullback.snd g G.t ≫ G.s)
                  (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                pullback.snd (g' ≫ g) G.t) ≫
                G.s =
              q ≫ G.s := by rw [hCandidateMiddle]
            _ = ((β ≫ pullback.snd g G.t) ≫ G.i) ≫ G.t := hCancel
            _ =
                (candidate ≫
                    ((pullback.fst (pullback.snd g G.t ≫ G.s)
                        (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                      pullback.snd g G.t) ≫
                      G.i)) ≫
                  G.t := by rw [hCandidateLeftInv]
        have hComposeCongr {a a' b b' : T ⟶ G.R}
            (ha : a = a') (hb : b = b')
            {haComp : a ≫ G.s = b ≫ G.t}
            {hbComp : a' ≫ G.s = b' ≫ G.t} :
            G.compose a b haComp = G.compose a' b' hbComp := by
          subst ha
          subst hb
          rfl
        have hCandidateCompose :
            G.compose
                (candidate ≫
                  pullback.snd (pullback.snd g G.t ≫ G.s)
                    (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                  pullback.snd (g' ≫ g) G.t)
                (candidate ≫
                  ((pullback.fst (pullback.snd g G.t ≫ G.s)
                      (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                    pullback.snd g G.t) ≫
                    G.i))
                hOuterComp =
              G.compose q ((β ≫ pullback.snd g G.t) ≫ G.i) hCancel := by
          exact hComposeCongr hCandidateMiddle hCandidateLeftInv
        have hFinalCancel :
            G.compose q ((β ≫ pullback.snd g G.t) ≫ G.i) hCancel =
              α ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫
                pullbackArrow G g := by
          simpa [q, Category.assoc] using
            (compose_cancel_right_inverse G
              (α ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g)
              (β ≫ pullback.snd g G.t)
              hcomp
              hCancel)
        calc
          candidate ≫ restrictionComparison G g g' ≫
              pullback.snd g' (G.toPreRelation.pullback g).t ≫
              pullbackArrow G g =
            candidate ≫
              G.compose
                (pullback.snd (pullback.snd g G.t ≫ G.s)
                    (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                  pullback.snd (g' ≫ g) G.t)
                ((pullback.fst (pullback.snd g G.t ≫ G.s)
                    (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                  pullback.snd g G.t) ≫
                  G.i)
                (restrictionComparisonComposable G g g') := by
                  simpa [Category.assoc] using
                    congrArg (fun k ↦ candidate ≫ k) (restrictionComparison_arrowImage G g g')
          _ = G.compose q ((β ≫ pullback.snd g G.t) ≫ G.i) hCancel := by
                have hCompCandidate :
                    candidate ≫
                        G.compose
                          (pullback.snd (pullback.snd g G.t ≫ G.s)
                              (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                            pullback.snd (g' ≫ g) G.t)
                          ((pullback.fst (pullback.snd g G.t ≫ G.s)
                              (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                            pullback.snd g G.t) ≫
                            G.i)
                          (restrictionComparisonComposable G g g') =
                      G.compose
                        (candidate ≫
                          pullback.snd (pullback.snd g G.t ≫ G.s)
                            (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                          pullback.snd (g' ≫ g) G.t)
                        (candidate ≫
                          ((pullback.fst (pullback.snd g G.t ≫ G.s)
                              (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                            pullback.snd g G.t) ≫
                            G.i))
                        hOuterComp := by
                  exact
                    comp_compose G candidate
                      (pullback.snd (pullback.snd g G.t ≫ G.s)
                        (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                          pullback.snd (g' ≫ g) G.t)
                      ((pullback.fst (pullback.snd g G.t ≫ G.s)
                        (pullback.snd (g' ≫ g) G.t ≫ G.s) ≫
                          pullback.snd g G.t) ≫
                          G.i)
                      (restrictionComparisonComposable G g g')
                      hOuterComp
                exact hCompCandidate.trans hCandidateCompose
          _ = α ≫ pullback.snd g' (G.toPreRelation.pullback g).t ≫ pullbackArrow G g := by
                exact hFinalCancel
    refine ⟨candidate, hCandidateTop, hCandidate_fst⟩

/-- The square formed by the two source maps from the pullback of successive
restrictions is cartesian. -/
theorem restrictionComparisonRightIsPullback {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    IsPullback
      (pullback.snd (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s))
      (pullback.fst (pullback.snd g G.t ≫ G.s)
        (pullback.snd (g' ≫ g) G.t ≫ G.s))
      (pullback.snd (g' ≫ g) G.t ≫ G.s)
      (pullback.snd g G.t ≫ G.s) :=
  (IsPullback.of_hasPullback
    (pullback.snd g G.t ≫ G.s)
    (pullback.snd (g' ≫ g) G.t ≫ G.s)).flip

/-- For two successive restrictions of a groupoid scheme, the canonical comparison diagram
has both squares cartesian. -/
theorem iteratedRestrictionDiagram {S : Scheme.{u}} (G : GroupoidScheme S)
    {U' U'' : Over S} (g : U' ⟶ G.U) (g' : U'' ⟶ U') :
    IsPullback (restrictionComparison G g g')
        (pullback.fst (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s))
        (pullback.snd g' (G.pullback g).t ≫ (G.pullback g).s)
        (pullback.fst g G.t) ∧
      IsPullback
        (pullback.snd (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s))
        (pullback.fst (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s))
        (pullback.snd (g' ≫ g) G.t ≫ G.s)
        (pullback.snd g G.t ≫ G.s) :=
  ⟨restrictionComparisonLeftIsPullback G g g',
    restrictionComparisonRightIsPullback G g g'⟩

end AlgebraicGeometry.GroupoidScheme
