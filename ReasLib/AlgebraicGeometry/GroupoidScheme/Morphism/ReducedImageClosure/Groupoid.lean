module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.ReducedImageClosure
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.Product

/-!
# Reduced image-closure groupoids

An identity-on-objects morphism of groupoid schemes over the spectrum of a perfect field
induces a groupoid structure on the reduced closure of its arrow-map image.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.Hom

/-- The vanishing ideal of the reduced arrow-image closure is contained in the kernel of
the target identity map. -/
theorem reducedImageClosureIdentity_condition
    {S : Scheme.{u}} {k : Type u} [Field k] {G₁ G₂ : GroupoidScheme S}
    (eU : Spec (CommRingCat.of k) ≅ G₁.U.left) (hU : G₁.U = G₂.U)
    (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left)) ≤
      Scheme.Hom.ker G₂.e.left := by
  let eU₂ : Spec (CommRingCat.of k) ≅ G₂.U.left :=
    eU.trans (eqToIso (congrArg Over.left hU))
  -- Local instance justification (proof-local temporary data): the ideal factorization
  -- criterion needs reducedness transported across the specified object-scheme isomorphism.
  let _ : IsReduced G₂.U.left := by
    -- Transport reducedness from `Spec k` across the chosen object-scheme isomorphism.
    exact CategoryTheory.ObjectProperty.prop_of_iso (IsReduced ·) eU₂ inferInstance
  rw [Scheme.IdealSheafData.le_ker_iff_range_subset,
    Scheme.IdealSheafData.support_vanishingIdeal]
  intro r hr
  rcases hr with ⟨u, rfl⟩
  -- Every target identity arrow already lies in the original arrow-image.
  refine subset_closure ?_
  let u₁ : G₁.U.left := (Over.Hom.left (eqToHom hU.symm)) u
  refine ⟨G₁.e.left u₁, ?_⟩
  have hMapE :
      G₁.e.left ≫ f.arrow.left =
        Over.Hom.left (eqToHom hU) ≫ G₂.e.left := by
    have hObj : f.obj = eqToHom hU := hf
    simpa [hObj, Category.assoc] using congrArg Over.Hom.left (Hom.map_e f)
  have hEval :
      f.arrow.left (G₁.e.left u₁) =
        G₂.e.left ((Over.Hom.left (eqToHom hU)) u₁) := by
    exact congrArg (fun g : G₁.U.left ⟶ G₂.R.left => g u₁) hMapE
  have hu₁ : (Over.Hom.left (eqToHom hU)) u₁ = u := by
    change (Over.Hom.left (eqToHom hU.symm ≫ eqToHom hU)) u = u
    simpa using
      congrArg (fun g : G₂.U.left ⟶ G₂.U.left => g u)
        (congrArg Over.Hom.left (eqToHom_trans hU.symm hU))
  calc
    f.arrow.left (G₁.e.left u₁) =
      G₂.e.left ((Over.Hom.left (eqToHom hU)) u₁) := hEval
    _ = G₂.e.left u := by rw [hu₁]

/-- The canonical lift of the target identity map to the reduced arrow-image closure lies
over the base scheme. -/
theorem reducedImageClosureIdentity_over
    {S : Scheme.{u}} {k : Type u} [Field k] {G₁ G₂ : GroupoidScheme S}
    (eU : Spec (CommRingCat.of k) ≅ G₁.U.left) (hU : G₁.U = G₂.U)
    (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift G₂.e.left
          (reducedImageClosureIdentity_condition eU hU f hf) ≫
        (Scheme.Hom.reducedImageClosureOver f.arrow).hom = G₂.U.hom := by
  -- The scheme-level lift remains over `S` because the target identity is over `S`.
  have hLift :
      (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
          G₂.e.left
          (reducedImageClosureIdentity_condition eU hU f hf) ≫
        (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι =
      G₂.e.left :=
    Scheme.IdealSheafData.lift_subschemeι
      (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left)))
      G₂.e.left
      (reducedImageClosureIdentity_condition eU hU f hf)
  calc
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
        G₂.e.left
        (reducedImageClosureIdentity_condition eU hU f hf) ≫
        (Scheme.Hom.reducedImageClosureOver f.arrow).hom
      =
        (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
            G₂.e.left
            (reducedImageClosureIdentity_condition eU hU f hf) ≫
          (Scheme.IdealSheafData.vanishingIdeal
            (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι ≫
          G₂.R.hom := by
            rfl
    _ = G₂.e.left ≫ G₂.R.hom := by
          simpa [Category.assoc] using congrArg (fun g ↦ g ≫ G₂.R.hom) hLift
    _ = G₂.U.hom := Over.w G₂.e

/-- The identity map of the target groupoid, canonically lifted to the reduced arrow-image
closure. -/
noncomputable def reducedImageClosureIdentity
    {S : Scheme.{u}} {k : Type u} [Field k] {G₁ G₂ : GroupoidScheme S}
    (eU : Spec (CommRingCat.of k) ≅ G₁.U.left) (hU : G₁.U = G₂.U)
    (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    G₂.U ⟶ Scheme.Hom.reducedImageClosureOver f.arrow :=
  Over.homMk
    ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift G₂.e.left
        (reducedImageClosureIdentity_condition eU hU f hf))
    (reducedImageClosureIdentity_over eU hU f hf)

/-- The lifted identity followed by the reduced-closure inclusion is the target identity
map. -/
theorem reducedImageClosureIdentity_toArrows
    {S : Scheme.{u}} {k : Type u} [Field k] {G₁ G₂ : GroupoidScheme S}
    (eU : Spec (CommRingCat.of k) ≅ G₁.U.left) (hU : G₁.U = G₂.U)
    (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    reducedImageClosureIdentity eU hU f hf ≫
      Scheme.Hom.reducedImageClosureιOver f.arrow = G₂.e := by
  apply Over.OverMorphism.ext
  -- Forgetting to schemes identifies the lifted identity with the ambient identity.
  change
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
        G₂.e.left
        (reducedImageClosureIdentity_condition eU hU f hf) ≫
        (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι =
      G₂.e.left
  exact Scheme.IdealSheafData.lift_subschemeι
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left)))
    G₂.e.left
    (reducedImageClosureIdentity_condition eU hU f hf)

/-- The vanishing ideal of the reduced arrow-image closure is contained in the kernel of
the target inversion restricted to that closure. -/
theorem reducedImageClosureInverse_condition
    {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S} (hU : G₁.U = G₂.U)
    (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left)) ≤
      ((Scheme.Hom.reducedImageClosureιOver f.arrow).left ≫ G₂.i.left).ker := by
  let _ := hf
  -- Local instance justification (proof-local temporary data): the ideal factorization
  -- criterion needs reducedness of the canonical reduced closed subscheme.
  let _ : IsReduced (Scheme.Hom.reducedImageClosureOver f.arrow).left := by
    change IsReduced
      ((Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subscheme)
    infer_instance
  rw [Scheme.IdealSheafData.le_ker_iff_range_subset,
    Scheme.IdealSheafData.support_vanishingIdeal]
  let A : Set G₂.R.left := Set.range f.arrow.left
  have hInvMaps : Set.MapsTo G₂.i.left A A := by
    intro r hr
    rcases hr with ⟨r₁, rfl⟩
    refine ⟨G₁.i.left r₁, ?_⟩
    -- The inverse map commutes with the arrow morphism.
    have hMapI : G₁.i.left ≫ f.arrow.left = f.arrow.left ≫ G₂.i.left := by
      simpa [Category.assoc] using congrArg Over.Hom.left (Hom.map_i f)
    exact congrArg (fun g : G₁.R.left ⟶ G₂.R.left => g r₁) hMapI
  intro r hr
  rcases hr with ⟨z, rfl⟩
  have hz : (Scheme.Hom.reducedImageClosureιOver f.arrow).left z ∈ closure A := by
    have hz' :
        (Scheme.Hom.reducedImageClosureιOver f.arrow).left z ∈
          Set.range (Scheme.Hom.reducedImageClosureιOver f.arrow).left := ⟨z, rfl⟩
    rwa [Scheme.Hom.range_reducedImageClosureιOver (f := f.arrow)] at hz'
  -- Continuity of inversion carries the closure of the arrow-image into itself.
  exact (hInvMaps.closure G₂.i.left.continuous) hz

/-- The canonical lift of target inversion to the reduced arrow-image closure lies over the
base scheme. -/
theorem reducedImageClosureInverse_over
    {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S} (hU : G₁.U = G₂.U)
    (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
          ((Scheme.Hom.reducedImageClosureιOver f.arrow).left ≫ G₂.i.left)
          (reducedImageClosureInverse_condition hU f hf) ≫
        (Scheme.Hom.reducedImageClosureOver f.arrow).hom =
      (Scheme.Hom.reducedImageClosureOver f.arrow).hom := by
  -- The inverse lift remains over `S` because target inversion is over `S`.
  have hLift :
      (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
          ((Scheme.Hom.reducedImageClosureιOver f.arrow).left ≫ G₂.i.left)
          (reducedImageClosureInverse_condition hU f hf) ≫
        (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι =
      (Scheme.Hom.reducedImageClosureιOver f.arrow).left ≫ G₂.i.left :=
    Scheme.IdealSheafData.lift_subschemeι
      (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left)))
      ((Scheme.Hom.reducedImageClosureιOver f.arrow).left ≫ G₂.i.left)
      (reducedImageClosureInverse_condition hU f hf)
  calc
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
        ((Scheme.Hom.reducedImageClosureιOver f.arrow).left ≫ G₂.i.left)
        (reducedImageClosureInverse_condition hU f hf) ≫
        (Scheme.Hom.reducedImageClosureOver f.arrow).hom
      =
        (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
            ((Scheme.Hom.reducedImageClosureιOver f.arrow).left ≫ G₂.i.left)
            (reducedImageClosureInverse_condition hU f hf) ≫
          (Scheme.IdealSheafData.vanishingIdeal
            (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι ≫
          G₂.R.hom := by
            rfl
    _ = (Scheme.Hom.reducedImageClosureιOver f.arrow).left ≫ G₂.i.left ≫ G₂.R.hom := by
          simpa [Category.assoc] using congrArg (fun g ↦ g ≫ G₂.R.hom) hLift
    _ = (Scheme.Hom.reducedImageClosureOver f.arrow).hom := by
          simpa [Scheme.Hom.reducedImageClosureOver, Category.assoc] using
            congrArg
              (fun g ↦
                (Scheme.IdealSheafData.vanishingIdeal
                  (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι ≫ g)
              (Over.w G₂.i)

/-- Target inversion, canonically restricted to the reduced arrow-image closure. -/
noncomputable def reducedImageClosureInverse
    {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S} (hU : G₁.U = G₂.U)
    (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    Scheme.Hom.reducedImageClosureOver f.arrow ⟶
      Scheme.Hom.reducedImageClosureOver f.arrow :=
  Over.homMk
    ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
        ((Scheme.Hom.reducedImageClosureιOver f.arrow).left ≫ G₂.i.left)
        (reducedImageClosureInverse_condition hU f hf))
    (reducedImageClosureInverse_over hU f hf)

/-- Restricted inversion followed by the reduced-closure inclusion is the inclusion followed
by target inversion. -/
theorem reducedImageClosureInverse_toArrows
    {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S} (hU : G₁.U = G₂.U)
    (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    reducedImageClosureInverse hU f hf ≫
      Scheme.Hom.reducedImageClosureιOver f.arrow =
      Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.i := by
  apply Over.OverMorphism.ext
  -- Forgetting to schemes identifies the restricted inverse with target inversion.
  change
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
        ((Scheme.Hom.reducedImageClosureιOver f.arrow).left ≫ G₂.i.left)
        (reducedImageClosureInverse_condition hU f hf) ≫
        (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι =
      (Scheme.Hom.reducedImageClosureιOver f.arrow).left ≫ G₂.i.left
  exact Scheme.IdealSheafData.lift_subschemeι
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left)))
    ((Scheme.Hom.reducedImageClosureιOver f.arrow).left ≫ G₂.i.left)
    (reducedImageClosureInverse_condition hU f hf)

/-- Over a perfect field, the pullback of the restricted source and target maps is reduced. -/
theorem reducedImageClosureComposablePullback_isReduced
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) :
    IsReduced
      (Limits.pullback
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s).left
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t).left : Scheme) := by
  let eU₂ : Spec (CommRingCat.of k) ≅ G₂.U.left :=
    eU.trans (eqToIso (congrArg Over.left hU))
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  let s' : (Scheme.Hom.reducedImageClosureOver f.arrow).left ⟶ G₂.U.left := (i ≫ G₂.s).left
  let t' : (Scheme.Hom.reducedImageClosureOver f.arrow).left ⟶ G₂.U.left := (i ≫ G₂.t).left
  let X : Over (Spec (CommRingCat.of k)) := Over.mk ((i ≫ G₂.s).left ≫ eU₂.inv)
  let Y : Over (Spec (CommRingCat.of k)) := Over.mk ((i ≫ G₂.t).left ≫ eU₂.inv)
  -- Local instance justification (proof-local temporary data): the pullback comparison
  -- requires the inverse of the specified isomorphism to be mono.
  let _ : Mono eU₂.inv := by infer_instance
  -- Local instance justification (proof-local temporary data): reducedness of the first
  -- factor is needed only for this perfect-field pullback argument.
  let _ :
      IsReduced X.left := by
    dsimp [X]
    change
      IsReduced
        ((Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subscheme : Scheme)
    infer_instance
  -- Local instance justification (proof-local temporary data): reducedness of the second
  -- factor is needed only for this perfect-field pullback argument.
  let _ :
      IsReduced Y.left := by
    dsimp [Y]
    change
      IsReduced
        ((Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subscheme : Scheme)
    infer_instance
  -- Local instance justification (proof-local temporary data): the comparison-isomorphism
  -- argument consumes reducedness of this auxiliary pullback.
  let _ : IsReduced (Limits.pullback X.hom Y.hom : Scheme) :=
    SchemeOverField.isReduced_pullback_of_isReduced_of_perfectField X Y
  let ePull :=
    ((pullbackIsPullbackOfCompMono s' t' eU₂.inv).conePointUniqueUpToIso
      (limit.isLimit (cospan X.hom Y.hom))).symm
  -- The mono base-change comparison identifies the original pullback with the
  -- pullback over `Spec k`, so reducedness transports across that comparison isomorphism.
  exact CategoryTheory.ObjectProperty.prop_of_iso (IsReduced ·) ePull
    (SchemeOverField.isReduced_pullback_of_isReduced_of_perfectField X Y)

/-- Over a perfect field, the reduced arrow-image closure's composable-pair scheme factors
through the reduced arrow-image closure under target composition. -/
theorem reducedImageClosureCompositionLift_condition
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left)) ≤
      (reducedImageClosureComposition f).left.ker := by
  have hReduced :
      IsReduced
        (Limits.pullback
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s).left
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t).left : Scheme) :=
    reducedImageClosureComposablePullback_isReduced eU hU f
  let ePullback :=
    CategoryTheory.Limits.PreservesPullback.iso (CategoryTheory.Over.forget S)
      (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
      (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)
  -- Local instance justification (proof-local temporary data): the factorization criterion
  -- needs reducedness transported from the underlying scheme pullback.
  let _ :
      IsReduced
        (Limits.pullback
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)).left := by
    exact CategoryTheory.ObjectProperty.prop_of_iso (IsReduced ·) ePullback.symm hReduced
  -- Reducedness of the composable-pair source lets the factorization criterion
  -- reduce the claim to the already-proved set-theoretic range containment.
  rw [Scheme.IdealSheafData.le_ker_iff_range_subset,
    Scheme.IdealSheafData.support_vanishingIdeal]
  simpa [Scheme.Hom.range_reducedImageClosureιOver (f := f.arrow)] using
    reducedImageClosureComposition_range_subset eU hU f hf

/-- The canonical lift of restricted composition to the reduced arrow-image closure lies over
the base scheme. -/
theorem reducedImageClosureCompositionLift_over
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
          (reducedImageClosureComposition f).left
          (reducedImageClosureCompositionLift_condition eU hU f hf) ≫
        (Scheme.Hom.reducedImageClosureOver f.arrow).hom =
      (Limits.pullback
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)).hom := by
  -- The composition lift remains over `S` because ambient composition is over `S`.
  calc
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
        (reducedImageClosureComposition f).left
        (reducedImageClosureCompositionLift_condition eU hU f hf) ≫
        (Scheme.Hom.reducedImageClosureOver f.arrow).hom
      =
        (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
            (reducedImageClosureComposition f).left
            (reducedImageClosureCompositionLift_condition eU hU f hf) ≫
          (Scheme.IdealSheafData.vanishingIdeal
            (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι ≫
          G₂.R.hom := by
            rfl
    _ = (reducedImageClosureComposition f).left ≫ G₂.R.hom := by
          have hLift :
              (Scheme.IdealSheafData.vanishingIdeal
                (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
                  (reducedImageClosureComposition f).left
                  (reducedImageClosureCompositionLift_condition eU hU f hf) ≫
                (Scheme.IdealSheafData.vanishingIdeal
                  (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι =
              (reducedImageClosureComposition f).left :=
            Scheme.IdealSheafData.lift_subschemeι
              (Scheme.IdealSheafData.vanishingIdeal
                (TopologicalSpace.Closeds.closure (Set.range f.arrow.left)))
              (reducedImageClosureComposition f).left
              (reducedImageClosureCompositionLift_condition eU hU f hf)
          simpa [Category.assoc] using congrArg (fun g ↦ g ≫ G₂.R.hom) hLift
    _ = (Limits.pullback
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)).hom := by
          simpa [Category.assoc] using (Over.w (reducedImageClosureComposition f))

/-- Target composition, canonically restricted to composable arrows in the reduced
arrow-image closure. -/
noncomputable def reducedImageClosureCompositionLift
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    Limits.pullback
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) ⟶
      Scheme.Hom.reducedImageClosureOver f.arrow :=
  Over.homMk
    ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
        (reducedImageClosureComposition f).left
        (reducedImageClosureCompositionLift_condition eU hU f hf))
    (reducedImageClosureCompositionLift_over eU hU f hf)

/-- Restricted composition followed by the reduced-closure inclusion is target composition
on the corresponding composable arrows. -/
theorem reducedImageClosureCompositionLift_toArrows
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    reducedImageClosureCompositionLift eU hU f hf ≫
      Scheme.Hom.reducedImageClosureιOver f.arrow =
      reducedImageClosureComposition f := by
  apply Over.OverMorphism.ext
  -- Forgetting to schemes identifies the restricted composition with ambient composition.
  change
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).lift
        (reducedImageClosureComposition f).left
        (reducedImageClosureCompositionLift_condition eU hU f hf) ≫
        (Scheme.IdealSheafData.vanishingIdeal
          (TopologicalSpace.Closeds.closure (Set.range f.arrow.left))).subschemeι =
      (reducedImageClosureComposition f).left
  exact Scheme.IdealSheafData.lift_subschemeι
    (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f.arrow.left)))
    (reducedImageClosureComposition f).left
    (reducedImageClosureCompositionLift_condition eU hU f hf)

/-- Pointwise restricted composition agrees with ambient target-groupoid composition after
postcomposing with the reduced-closure inclusion. -/
theorem reducedImageClosureCompose_eq
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    {T : Over S} (a b : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow)
    (h : a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
      b ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) :
    pullback.lift a b h ≫ reducedImageClosureCompositionLift eU hU f hf ≫
        Scheme.Hom.reducedImageClosureιOver f.arrow =
      G₂.compose (a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
        (b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
        (by simpa [Category.assoc] using h) := by
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  have hLift :
      pullback.lift a b h ≫
          pullback.map (i ≫ G₂.s) (i ≫ G₂.t) G₂.s G₂.t i i (𝟙 G₂.U)
            (Category.comp_id _) (Category.comp_id _) =
        pullback.lift (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h) := by
    apply pullback.hom_ext
    · calc
        pullback.lift a b h ≫
            pullback.map (i ≫ G₂.s) (i ≫ G₂.t) G₂.s G₂.t i i (𝟙 G₂.U)
              (Category.comp_id _) (Category.comp_id _) ≫
            pullback.fst G₂.s G₂.t =
          pullback.lift a b h ≫ pullback.fst (i ≫ G₂.s) (i ≫ G₂.t) ≫ i := by
            exact congrArg
              (fun g ↦ pullback.lift a b h ≫ g)
              (pullback.lift_fst
                (pullback.fst (i ≫ G₂.s) (i ≫ G₂.t) ≫ i)
                (pullback.snd (i ≫ G₂.s) (i ≫ G₂.t) ≫ i)
                (by
                  simpa [Category.assoc] using
                    (pullback.condition_assoc
                      (f := i ≫ G₂.s) (g := i ≫ G₂.t) (h := 𝟙 G₂.U))))
        _ = a ≫ i := by
              simpa [Category.assoc] using congrArg (fun g ↦ g ≫ i) (pullback.lift_fst a b h)
        _ = pullback.lift (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h) ≫
              pullback.fst G₂.s G₂.t := by
              symm
              exact pullback.lift_fst (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h)
    · calc
        pullback.lift a b h ≫
            pullback.map (i ≫ G₂.s) (i ≫ G₂.t) G₂.s G₂.t i i (𝟙 G₂.U)
              (Category.comp_id _) (Category.comp_id _) ≫
            pullback.snd G₂.s G₂.t =
          pullback.lift a b h ≫ pullback.snd (i ≫ G₂.s) (i ≫ G₂.t) ≫ i := by
            exact congrArg
              (fun g ↦ pullback.lift a b h ≫ g)
              (pullback.lift_snd
                (pullback.fst (i ≫ G₂.s) (i ≫ G₂.t) ≫ i)
                (pullback.snd (i ≫ G₂.s) (i ≫ G₂.t) ≫ i)
                (by
                  simpa [Category.assoc] using
                    (pullback.condition_assoc
                      (f := i ≫ G₂.s) (g := i ≫ G₂.t) (h := 𝟙 G₂.U))))
        _ = b ≫ i := by
              simpa [Category.assoc] using congrArg (fun g ↦ g ≫ i) (pullback.lift_snd a b h)
        _ = pullback.lift (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h) ≫
              pullback.snd G₂.s G₂.t := by
              symm
              exact pullback.lift_snd (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h)
  -- The two pullback lifts agree on both projections, so restricted composition
  -- becomes ordinary ambient composition after postcomposing with the inclusion.
  calc
    pullback.lift a b h ≫ reducedImageClosureCompositionLift eU hU f hf ≫ i =
      pullback.lift a b h ≫ reducedImageClosureComposition f := by
        simpa [Category.assoc] using
          congrArg (fun g ↦ pullback.lift a b h ≫ g)
            (reducedImageClosureCompositionLift_toArrows eU hU f hf)
    _ =
      pullback.lift a b h ≫
        pullback.map (i ≫ G₂.s) (i ≫ G₂.t) G₂.s G₂.t i i (𝟙 G₂.U)
          (Category.comp_id _) (Category.comp_id _) ≫ G₂.c := by
          rfl
    _ =
      pullback.lift (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h) ≫ G₂.c := by
          simpa [Category.assoc] using congrArg (fun g ↦ g ≫ G₂.c) hLift
    _ = G₂.compose (a ≫ i) (b ≫ i) (by simpa [Category.assoc] using h) := rfl

/-- After postcomposing with the reduced-closure inclusion, restricted composition has the
source of the earlier arrow. -/
theorem reducedImageClosureCompose_source_eq
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    {T : Over S} (a b : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow)
    (h : a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
      b ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) :
    pullback.lift a b h ≫ reducedImageClosureCompositionLift eU hU f hf ≫
        Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s =
      b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s := by
  -- Once restricted composition is rewritten into ambient composition, the
  -- source formula is exactly the ambient `compose_source` law.
  calc
    pullback.lift a b h ≫ reducedImageClosureCompositionLift eU hU f hf ≫
        Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s =
      G₂.compose
          (a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
          (b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
          (by simpa [Category.assoc] using h) ≫
        G₂.s := by
          simpa [Category.assoc] using
            congrArg (fun g ↦ g ≫ G₂.s)
              (reducedImageClosureCompose_eq eU hU f hf a b h)
    _ = b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s := by
          simpa [Category.assoc] using
            G₂.compose_source
              (a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
              (b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
              (by simpa [Category.assoc] using h)

/-- After postcomposing with the reduced-closure inclusion, restricted composition has the
target of the later arrow. -/
theorem reducedImageClosureCompose_target_eq
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    {T : Over S} (a b : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow)
    (h : a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
      b ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) :
    pullback.lift a b h ≫ reducedImageClosureCompositionLift eU hU f hf ≫
        Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t =
      a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t := by
  -- The target formula is the ambient `compose_target` law after the same
  -- inclusion-based normalization.
  calc
    pullback.lift a b h ≫ reducedImageClosureCompositionLift eU hU f hf ≫
        Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t =
      G₂.compose
          (a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
          (b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
          (by simpa [Category.assoc] using h) ≫
        G₂.t := by
          simpa [Category.assoc] using
            congrArg (fun g ↦ g ≫ G₂.t)
              (reducedImageClosureCompose_eq eU hU f hf a b h)
    _ = a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t := by
          simpa [Category.assoc] using
            G₂.compose_target
              (a ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
              (b ≫ Scheme.Hom.reducedImageClosureιOver f.arrow)
              (by simpa [Category.assoc] using h)

/-- Equality into the reduced image closure can be checked after postcomposing with the
closed-subscheme inclusion. -/
theorem reducedImageClosureInclusion_cancel
    {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S} (f : Hom G₁ G₂)
    {T : Over S} {x y : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow}
    (h :
      x ≫ Scheme.Hom.reducedImageClosureιOver f.arrow =
        y ≫ Scheme.Hom.reducedImageClosureιOver f.arrow) :
    x = y := sorry

/-- The restricted composition map has the expected source map. -/
theorem reducedImageClosure_comp_source
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    reducedImageClosureCompositionLift eU hU f hf ≫
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
      pullback.snd
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) ≫
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) := by
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  -- Collapse the self-lift of the pullback projections before applying the source formula.
  simpa [Category.assoc, i, pullback.lift_fst_snd (i ≫ G₂.s) (i ≫ G₂.t)] using
    reducedImageClosureCompose_source_eq eU hU f hf
      (a := pullback.fst (i ≫ G₂.s) (i ≫ G₂.t))
      (b := pullback.snd (i ≫ G₂.s) (i ≫ G₂.t))
      (h := pullback.condition (f := i ≫ G₂.s) (g := i ≫ G₂.t))

/-- The restricted composition map has the expected target map. -/
theorem reducedImageClosure_comp_target
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    reducedImageClosureCompositionLift eU hU f hf ≫
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) =
      pullback.fst
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) ≫
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) := by
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  -- Collapse the self-lift of the pullback projections before applying the target formula.
  simpa [Category.assoc, i, pullback.lift_fst_snd (i ≫ G₂.s) (i ≫ G₂.t)] using
    reducedImageClosureCompose_target_eq eU hU f hf
      (a := pullback.fst (i ≫ G₂.s) (i ≫ G₂.t))
      (b := pullback.snd (i ≫ G₂.s) (i ≫ G₂.t))
      (h := pullback.condition (f := i ≫ G₂.s) (g := i ≫ G₂.t))

/-- The restricted composition law is associative after transporting both sides to the
ambient target groupoid. -/
theorem reducedImageClosure_associativity
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    {T : Over S} (a b d : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow)
    (h_ab : a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
      b ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t))
    (h_bd : b ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
      d ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t))
    (h_ab_d :
      (pullback.lift a b h_ab ≫ reducedImageClosureCompositionLift eU hU f hf) ≫
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
        d ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t))
    (h_a_bd :
      a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
        (pullback.lift b d h_bd ≫ reducedImageClosureCompositionLift eU hU f hf) ≫
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) :
    pullback.lift
        (pullback.lift a b h_ab ≫ reducedImageClosureCompositionLift eU hU f hf)
        d h_ab_d ≫
      reducedImageClosureCompositionLift eU hU f hf =
    pullback.lift
        a
        (pullback.lift b d h_bd ≫ reducedImageClosureCompositionLift eU hU f hf)
        h_a_bd ≫
      reducedImageClosureCompositionLift eU hU f hf := by
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  have h_ab' : a ≫ i ≫ G₂.s = b ≫ i ≫ G₂.t := by
    simpa [Category.assoc, i] using h_ab
  have h_bd' : b ≫ i ≫ G₂.s = d ≫ i ≫ G₂.t := by
    simpa [Category.assoc, i] using h_bd
  have h_inner_ab :
      pullback.lift a b h_ab ≫ reducedImageClosureCompositionLift eU hU f hf ≫ i =
        G₂.compose (a ≫ i) (b ≫ i) h_ab' := by
    simpa [Category.assoc, i] using reducedImageClosureCompose_eq eU hU f hf a b h_ab
  have h_inner_bd :
      pullback.lift b d h_bd ≫ reducedImageClosureCompositionLift eU hU f hf ≫ i =
        G₂.compose (b ≫ i) (d ≫ i) h_bd' := by
    simpa [Category.assoc, i] using reducedImageClosureCompose_eq eU hU f hf b d h_bd
  have h_ab_d' :
      G₂.compose (a ≫ i) (b ≫ i) h_ab' ≫ G₂.s = d ≫ i ≫ G₂.t := by
    calc
      G₂.compose (a ≫ i) (b ≫ i) h_ab' ≫ G₂.s =
        pullback.lift a b h_ab ≫ reducedImageClosureCompositionLift eU hU f hf ≫ i ≫ G₂.s := by
          simpa [Category.assoc, i] using
            congrArg (fun g ↦ g ≫ G₂.s) h_inner_ab.symm
      _ = d ≫ i ≫ G₂.t := by
            simpa [Category.assoc, i] using h_ab_d
  have h_a_bd' :
      a ≫ i ≫ G₂.s = G₂.compose (b ≫ i) (d ≫ i) h_bd' ≫ G₂.t := by
    calc
      a ≫ i ≫ G₂.s =
        (pullback.lift b d h_bd ≫ reducedImageClosureCompositionLift eU hU f hf) ≫ i ≫ G₂.t := by
          simpa [Category.assoc, i] using h_a_bd
      _ = G₂.compose (b ≫ i) (d ≫ i) h_bd' ≫ G₂.t := by
            simpa [Category.assoc, i] using
              congrArg (fun g ↦ g ≫ G₂.t) h_inner_bd
  -- Cancel the inclusion and compare both nested composites inside `G₂`,
  -- where associativity is already available.
  apply reducedImageClosureInclusion_cancel f
  calc
    pullback.lift
          (pullback.lift a b h_ab ≫ reducedImageClosureCompositionLift eU hU f hf)
          d h_ab_d ≫
        reducedImageClosureCompositionLift eU hU f hf ≫
        i =
      G₂.compose
          (G₂.compose (a ≫ i) (b ≫ i) h_ab')
          (d ≫ i) h_ab_d' := by
          simpa [Category.assoc, i, h_inner_ab] using
            reducedImageClosureCompose_eq eU hU f hf
              (pullback.lift a b h_ab ≫ reducedImageClosureCompositionLift eU hU f hf)
              d h_ab_d
    _ =
      G₂.compose
          (a ≫ i)
          (G₂.compose (b ≫ i) (d ≫ i) h_bd') h_a_bd' := by
          simpa using
            G₂.compose_assoc (a ≫ i) (b ≫ i) (d ≫ i) h_ab' h_bd' h_ab_d' h_a_bd'
    _ =
      pullback.lift
          a
          (pullback.lift b d h_bd ≫ reducedImageClosureCompositionLift eU hU f hf)
          h_a_bd ≫
        reducedImageClosureCompositionLift eU hU f hf ≫
        i := by
          simpa [Category.assoc, i, h_inner_bd] using
            (reducedImageClosureCompose_eq eU hU f hf
              a
              (pullback.lift b d h_bd ≫ reducedImageClosureCompositionLift eU hU f hf)
              h_a_bd).symm

/-- The restricted composition has the expected right identity law. -/
theorem reducedImageClosure_right_identity
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    {T : Over S} (a : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow)
    (h :
      a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
        ((a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)) ≫
            reducedImageClosureIdentity eU hU f hf) ≫
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) :
    pullback.lift
        a
        ((a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)) ≫
          reducedImageClosureIdentity eU hU f hf)
        h ≫
      reducedImageClosureCompositionLift eU hU f hf = a := sorry

/-- The restricted composition has the expected left identity law. -/
theorem reducedImageClosure_left_identity
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    {T : Over S} (a : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow)
    (h :
      (((a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) ≫
            reducedImageClosureIdentity eU hU f hf) ≫
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)) =
        a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) :
    pullback.lift
        ((a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) ≫
          reducedImageClosureIdentity eU hU f hf)
        a h ≫
      reducedImageClosureCompositionLift eU hU f hf = a := sorry

/-- The restricted inverse composed on the right gives the restricted identity at the target. -/
theorem reducedImageClosure_inverse_comp
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    {T : Over S} (a : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow)
    (h :
      a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
        (a ≫ reducedImageClosureInverse hU f hf) ≫
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) :
    pullback.lift a (a ≫ reducedImageClosureInverse hU f hf) h ≫
      reducedImageClosureCompositionLift eU hU f hf =
    (a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) ≫
      reducedImageClosureIdentity eU hU f hf := by
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  have h_inverse_arrow :
      (a ≫ reducedImageClosureInverse hU f hf) ≫ i =
        (a ≫ i) ≫ G₂.i := by
    simpa [Category.assoc, i] using
      congrArg (fun g ↦ a ≫ g) (reducedImageClosureInverse_toArrows hU f hf)
  have h_identity_arrow :
      ((a ≫ (i ≫ G₂.t)) ≫ reducedImageClosureIdentity eU hU f hf) ≫ i =
        (a ≫ i ≫ G₂.t) ≫ G₂.e := by
    simpa [Category.assoc, i] using
      congrArg (fun g ↦ (a ≫ i ≫ G₂.t) ≫ g)
        (reducedImageClosureIdentity_toArrows eU hU f hf)
  have h' :
      a ≫ i ≫ G₂.s = ((a ≫ i) ≫ G₂.i) ≫ G₂.t := by
    calc
      a ≫ i ≫ G₂.s =
        ((a ≫ reducedImageClosureInverse hU f hf) ≫ i) ≫ G₂.t := by
          simpa [Category.assoc, i] using h
      _ = ((a ≫ i) ≫ G₂.i) ≫ G₂.t := by
            simpa [Category.assoc, i] using congrArg (fun g ↦ g ≫ G₂.t) h_inverse_arrow
  -- Normalize both the inverse arrow and the target identity after inclusion,
  -- then apply the ambient `compose_inverse` law.
  apply reducedImageClosureInclusion_cancel f
  calc
    pullback.lift a (a ≫ reducedImageClosureInverse hU f hf) h ≫
        reducedImageClosureCompositionLift eU hU f hf ≫
        i =
      G₂.compose
          (a ≫ i)
          ((a ≫ reducedImageClosureInverse hU f hf) ≫ i)
          (by simpa [Category.assoc, i] using h) := by
          simpa [Category.assoc, i] using
            reducedImageClosureCompose_eq eU hU f hf
              a (a ≫ reducedImageClosureInverse hU f hf) h
    _ = G₂.compose (a ≫ i) ((a ≫ i) ≫ G₂.i) h' := by
          simpa [Category.assoc, i, h_inverse_arrow]
    _ = (a ≫ i ≫ G₂.t) ≫ G₂.e := by
          simpa [Category.assoc] using G₂.compose_inverse (a ≫ i) h'
    _ = ((a ≫ (i ≫ G₂.t)) ≫ reducedImageClosureIdentity eU hU f hf) ≫ i := by
          simpa [Category.assoc, i] using h_identity_arrow.symm

/-- The restricted inverse composed on the left gives the restricted identity at the source. -/
theorem reducedImageClosure_comp_inverse
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU)
    {T : Over S} (a : T ⟶ Scheme.Hom.reducedImageClosureOver f.arrow)
    (h :
      (a ≫ reducedImageClosureInverse hU f hf) ≫
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
        a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)) :
    pullback.lift (a ≫ reducedImageClosureInverse hU f hf) a h ≫
      reducedImageClosureCompositionLift eU hU f hf =
    (a ≫ (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)) ≫
      reducedImageClosureIdentity eU hU f hf := by
  let i := Scheme.Hom.reducedImageClosureιOver f.arrow
  have h_inverse_arrow :
      (a ≫ reducedImageClosureInverse hU f hf) ≫ i =
        (a ≫ i) ≫ G₂.i := by
    simpa [Category.assoc, i] using
      congrArg (fun g ↦ a ≫ g) (reducedImageClosureInverse_toArrows hU f hf)
  have h_identity_arrow :
      ((a ≫ (i ≫ G₂.s)) ≫ reducedImageClosureIdentity eU hU f hf) ≫ i =
        (a ≫ i ≫ G₂.s) ≫ G₂.e := by
    simpa [Category.assoc, i] using
      congrArg (fun g ↦ (a ≫ i ≫ G₂.s) ≫ g)
        (reducedImageClosureIdentity_toArrows eU hU f hf)
  have h' :
      ((a ≫ i) ≫ G₂.i) ≫ G₂.s = a ≫ i ≫ G₂.t := by
    calc
      ((a ≫ i) ≫ G₂.i) ≫ G₂.s =
        ((a ≫ reducedImageClosureInverse hU f hf) ≫ i) ≫ G₂.s := by
          simpa [Category.assoc, i] using congrArg (fun g ↦ g ≫ G₂.s) h_inverse_arrow.symm
      _ = a ≫ i ≫ G₂.t := by
            simpa [Category.assoc, i] using h
  -- After rewriting the restricted inverse into the ambient inverse, the
  -- remaining equality is the ambient `inverse_compose` law.
  apply reducedImageClosureInclusion_cancel f
  calc
    pullback.lift (a ≫ reducedImageClosureInverse hU f hf) a h ≫
        reducedImageClosureCompositionLift eU hU f hf ≫
        i =
      G₂.compose
          ((a ≫ reducedImageClosureInverse hU f hf) ≫ i)
          (a ≫ i)
          (by simpa [Category.assoc, i] using h) := by
          simpa [Category.assoc, i] using
            reducedImageClosureCompose_eq eU hU f hf
              (a ≫ reducedImageClosureInverse hU f hf) a h
    _ = G₂.compose ((a ≫ i) ≫ G₂.i) (a ≫ i) h' := by
          simpa [Category.assoc, i, h_inverse_arrow]
    _ = (a ≫ i ≫ G₂.s) ≫ G₂.e := by
          simpa [Category.assoc] using G₂.inverse_compose (a ≫ i) h'
    _ = ((a ≫ (i ≫ G₂.s)) ≫ reducedImageClosureIdentity eU hU f hf) ≫ i := by
          simpa [Category.assoc, i] using h_identity_arrow.symm

/-- Over a perfect field, the reduced closed subscheme supported on the
closure of the arrow-map image inherits the source, target, composition, identity, and inverse
maps of a groupoid scheme over `S`. -/
noncomputable def reducedImageClosure
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    GroupoidScheme S where
  U := G₂.U
  R := Scheme.Hom.reducedImageClosureOver f.arrow
  s := Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s
  t := Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t
  c := reducedImageClosureCompositionLift eU hU f hf
  e := reducedImageClosureIdentity eU hU f hf
  i := reducedImageClosureInverse hU f hf
  comp_source := reducedImageClosure_comp_source eU hU f hf
  comp_target := reducedImageClosure_comp_target eU hU f hf
  identity_source := by
    -- The restricted identity becomes the ambient identity after the inclusion.
    calc
      reducedImageClosureIdentity eU hU f hf ≫
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
        G₂.e ≫ G₂.s := by
          simpa [Category.assoc] using
            congrArg (fun g ↦ g ≫ G₂.s)
              (reducedImageClosureIdentity_toArrows eU hU f hf)
      _ = 𝟙 G₂.U := G₂.identity_source
  identity_target := by
    -- The restricted identity becomes the ambient identity after the inclusion.
    calc
      reducedImageClosureIdentity eU hU f hf ≫
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) =
        G₂.e ≫ G₂.t := by
          simpa [Category.assoc] using
            congrArg (fun g ↦ g ≫ G₂.t)
              (reducedImageClosureIdentity_toArrows eU hU f hf)
      _ = 𝟙 G₂.U := G₂.identity_target
  inverse_source := by
    -- The restricted inverse inherits the source-target swap from `G₂`.
    calc
      reducedImageClosureInverse hU f hf ≫
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s) =
        Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.i ≫ G₂.s := by
          simpa [Category.assoc] using
            congrArg (fun g ↦ g ≫ G₂.s)
              (reducedImageClosureInverse_toArrows hU f hf)
      _ = Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t := by
          simpa [Category.assoc] using
            congrArg (fun g ↦ Scheme.Hom.reducedImageClosureιOver f.arrow ≫ g)
              G₂.inverse_source
  inverse_target := by
    -- The restricted inverse inherits the target-source swap from `G₂`.
    calc
      reducedImageClosureInverse hU f hf ≫
          (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t) =
        Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.i ≫ G₂.t := by
          simpa [Category.assoc] using
            congrArg (fun g ↦ g ≫ G₂.t)
              (reducedImageClosureInverse_toArrows hU f hf)
      _ = Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s := by
          simpa [Category.assoc] using
            congrArg (fun g ↦ Scheme.Hom.reducedImageClosureιOver f.arrow ≫ g)
              G₂.inverse_target
  associativity := reducedImageClosure_associativity eU hU f hf
  right_identity := reducedImageClosure_right_identity eU hU f hf
  left_identity := reducedImageClosure_left_identity eU hU f hf
  inverse_comp := reducedImageClosure_inverse_comp eU hU f hf
  comp_inverse := reducedImageClosure_comp_inverse eU hU f hf

/-- The inclusion morphism uses the same pullback map as the restricted composition
construction. -/
theorem reducedImageClosureInclusion_composableMap
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    GroupoidScheme.composableMap
        (G := reducedImageClosure eU hU f hf)
        (H := G₂)
        (𝟙 G₂.U)
        (Scheme.Hom.reducedImageClosureιOver f.arrow)
        (by simp [reducedImageClosure])
        (by simp [reducedImageClosure]) =
      pullback.map
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s)
        (Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t)
        G₂.s G₂.t
        (Scheme.Hom.reducedImageClosureιOver f.arrow)
        (Scheme.Hom.reducedImageClosureιOver f.arrow)
        (𝟙 G₂.U)
        (Category.comp_id _)
        (Category.comp_id _) := rfl

/-- The object scheme of the reduced image-closure groupoid is the target object scheme. -/
theorem reducedImageClosure_U
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (reducedImageClosure eU hU f hf).U = G₂.U := rfl

/-- The arrow scheme of the reduced image-closure groupoid is the canonical reduced closure
of the arrow-map image. -/
theorem reducedImageClosure_R
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (reducedImageClosure eU hU f hf).R =
      Scheme.Hom.reducedImageClosureOver f.arrow := rfl

/-- The source map of the reduced image-closure groupoid is target source restricted along
the canonical inclusion. -/
theorem reducedImageClosure_s
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (reducedImageClosure eU hU f hf).s =
      Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.s := rfl

/-- The target map of the reduced image-closure groupoid is target target restricted along
the canonical inclusion. -/
theorem reducedImageClosure_t
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (reducedImageClosure eU hU f hf).t =
      Scheme.Hom.reducedImageClosureιOver f.arrow ≫ G₂.t := rfl

/-- Composition in the reduced image-closure groupoid is the canonical lift of target
composition. -/
theorem reducedImageClosure_c
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (reducedImageClosure eU hU f hf).c =
      reducedImageClosureCompositionLift eU hU f hf := rfl

/-- The identity map of the reduced image-closure groupoid is the canonical lift of target
identity. -/
theorem reducedImageClosure_e
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (reducedImageClosure eU hU f hf).e =
      reducedImageClosureIdentity eU hU f hf := rfl

/-- The inverse map of the reduced image-closure groupoid is the canonical restriction of
target inversion. -/
theorem reducedImageClosure_i
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (reducedImageClosure eU hU f hf).i =
      reducedImageClosureInverse hU f hf := rfl

/-- The canonical inclusion of the reduced image-closure groupoid into the target groupoid. -/
noncomputable def reducedImageClosureι
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    Hom (reducedImageClosure eU hU f hf) G₂ where
  obj := 𝟙 G₂.U
  arrow := Scheme.Hom.reducedImageClosureιOver f.arrow
  map_s := by
    -- The restricted source map was defined by postcomposing with the inclusion.
    simp [reducedImageClosure]
  map_t := by
    -- The restricted target map was defined by postcomposing with the inclusion.
    simp [reducedImageClosure]
  map_c := sorry

/-- The canonical reduced-image-closure inclusion is the identity on objects. -/
theorem reducedImageClosureι_obj
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (reducedImageClosureι eU hU f hf).obj = 𝟙 G₂.U := rfl

/-- The arrow component of the canonical reduced-image-closure inclusion is the reduced
closed-subscheme inclusion. -/
theorem reducedImageClosureι_arrow
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (reducedImageClosureι eU hU f hf).arrow =
      Scheme.Hom.reducedImageClosureιOver f.arrow := rfl

/-- The canonical inclusion of the reduced image-closure groupoid is identity on objects. -/
theorem reducedImageClosureι_isIdentityOnObjects
    {S : Scheme.{u}} {k : Type u} [Field k] [PerfectField k]
    {G₁ G₂ : GroupoidScheme S} (eU : Spec (CommRingCat.of k) ≅ G₁.U.left)
    (hU : G₁.U = G₂.U) (f : Hom G₁ G₂) (hf : f.IsIdentityOnObjects hU) :
    (reducedImageClosureι eU hU f hf).IsIdentityOnObjects rfl := by
  -- The canonical inclusion is literally the identity on objects.
  rfl

end AlgebraicGeometry.GroupoidScheme.Hom
