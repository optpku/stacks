/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.ReducedImageClosure.Groupoid.IdentityInverse
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Morphism.ReducedImageClosure.Groupoid.Composition

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
