/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.ReducedImageClosure

/-!
# Identity and inverse on reduced image closures

This module constructs the canonical lifts of target identity and inversion to the reduced
closure of the arrow-map image, together with their compatibility with the inclusion.
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

end AlgebraicGeometry.GroupoidScheme.Hom
