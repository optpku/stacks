/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.Source
public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.Target
public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Map

/-! # Dual-number deformations of scheme morphisms -/

@[expose] public section
open CategoryTheory AlgebraicGeometry Functor Limits
open Functor.Fiber ArtinianLocalAlgCat
open scoped DualNumber
noncomputable section
universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeMorphismCat

/-- The trivial dual-number morphism `f' = f × id : X' ⟶ Y'`. -/
def trivialHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k)) (hf : f ≫ hY = hX) :
    FlatSchemeCat.trivialScheme Λ k X hX ⟶ FlatSchemeCat.trivialScheme Λ k Y hY :=
  pullback.lift (FlatSchemeCat.trivialSchemeProj Λ k X hX ≫ f)
    (FlatSchemeCat.trivialSchemeOver Λ k X hX) (by
      simpa only [FlatSchemeCat.trivialScheme, FlatSchemeCat.trivialSchemeProj, FlatSchemeCat.trivialSchemeOver,
        specMap, FlatSchemeCat.specMap, Category.assoc, hf] using
        (pullback.condition (f := hX) (g := FlatSchemeCat.specMap (residueToDualNumber Λ k))))

/-- `trivialHom` is the unique map over `Spec k[ε]` lifting `f`. -/
theorem trivialHom_spec {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k)) (hf : f ≫ hY = hX) :
    trivialHom Λ k f hX hY hf ≫ FlatSchemeCat.trivialSchemeProj Λ k Y hY =
      FlatSchemeCat.trivialSchemeProj Λ k X hX ≫ f := by
  exact pullback.lift_fst _ _ _

/-- The trivial dual-number object `(k[ε], X' ⟶ Y')` of `FlatSchemeMorphismCat`. -/
def trivialObj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    FlatSchemeMorphismCat Λ k :=
  of (dualNumber Λ k) (FlatSchemeCat.trivialScheme Λ k X hX) (FlatSchemeCat.trivialScheme Λ k Y hY)
    (trivialHom Λ k f hX hY hf) (FlatSchemeCat.trivialSchemeOver Λ k X hX) (FlatSchemeCat.trivialSchemeOver Λ k Y hY)
    (by exact pullback.lift_snd _ _ _)

/-- The trivial dual-number deformation of `x0 = (k, X ⟶ Y)` in the fibre of `forget`. -/
def trivialDeformation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    (forget Λ k).Fiber (dualNumber Λ k) :=
  Fiber.mk (rfl : (forget Λ k).obj (trivialObj Λ k f hX hY hf) = dualNumber Λ k)

/-- The canonical strongly cocartesian pushforward of `x0` along `k ⟶ k[ε]`. -/
def trivialPushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    fiberInclusion.obj (residueObj Λ k X Y f hX hY hf) ⟶
      fiberInclusion.obj (trivialDeformation Λ k f hX hY hf)  :=
  let laws :
      IsPullback (FlatSchemeCat.trivialSchemeProj Λ k X hX)
        (trivialHom Λ k f hX hY hf) f (FlatSchemeCat.trivialSchemeProj Λ k Y hY) ∧
      IsPullback (FlatSchemeCat.trivialSchemeProj Λ k Y hY)
        (FlatSchemeCat.trivialSchemeOver Λ k Y hY) hY
        (specMap (residueToDualNumber Λ k)) := by
    have hover : trivialHom Λ k f hX hY hf ≫ FlatSchemeCat.trivialSchemeOver Λ k Y hY =
        FlatSchemeCat.trivialSchemeOver Λ k X hX := pullback.lift_snd _ _ _
    constructor
    · apply IsPullback.of_bot (v₂₁ := FlatSchemeCat.trivialSchemeOver Λ k Y hY)
        (v₂₂ := hY) (h₃₁ := specMap (residueToDualNumber Λ k))
      · change IsPullback (FlatSchemeCat.trivialSchemeProj Λ k X hX)
          (trivialHom Λ k f hX hY hf ≫ FlatSchemeCat.trivialSchemeOver Λ k Y hY)
          (f ≫ hY) (FlatSchemeCat.specMap (residueToDualNumber Λ k))
        rw [hover, hf]
        exact IsPullback.of_hasPullback hX (specMap (residueToDualNumber Λ k))
      · exact (trivialHom_spec Λ k f hX hY hf).symm
      · exact IsPullback.of_hasPullback hY (specMap (residueToDualNumber Λ k))
    · exact IsPullback.of_hasPullback hY (specMap (residueToDualNumber Λ k))
  Hom.of (residueToDualNumber Λ k) (FlatSchemeCat.trivialSchemeProj Λ k X hX)
    (FlatSchemeCat.trivialSchemeProj Λ k Y hY) laws.1 laws.2

/-- The canonical pushforward of `x0` along `k ⟶ k[ε]` is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    (forget Λ k).IsStronglyCocartesian (residueToDualNumber Λ k)
      (trivialPushforward Λ k f hX hY hf) := by
  let p := forget Λ k
  let φ := trivialPushforward Λ k f hX hY hf
  have opLift {R S : ArtinianLocalAlgCat Λ k} {a b : FlatSchemeMorphismCat Λ k}
      {g : R ⟶ S} {ψ : a ⟶ b} (h : p.IsHomLift g ψ) :
      p.op.IsHomLift g.op ψ.op := by
    cases h
    exact IsHomLift.map _
  have unopLift {R S : (ArtinianLocalAlgCat Λ k)ᵒᵖ}
      {a b : (FlatSchemeMorphismCat Λ k)ᵒᵖ} {g : R ⟶ S} {ψ : a ⟶ b}
      (h : p.op.IsHomLift g ψ) : p.IsHomLift g.unop ψ.unop := by
    cases h
    exact IsHomLift.map _
  have certificate := IsFibered.InGroupoids.all_isStronglyCartesian (p := p.op) φ.op
  refine { toIsHomLift := IsHomLift.map φ, universal_property' := ?_ }
  intro target base arrow arrowLift
  have oppositeLift : p.op.IsHomLift (base.op ≫ (residueToDualNumber Λ k).op)
      arrow.op := by
    simpa only [op_comp] using opLift arrowLift
  obtain ⟨factor, ⟨factorLift, factorization⟩, uniqueness⟩ :=
    @IsStronglyCartesian.universal_property' _ _ _ _ p.op _ _ _ _
      (residueToDualNumber Λ k).op φ.op certificate
      (Opposite.op target) base.op arrow.op oppositeLift
  refine ⟨factor.unop, ⟨unopLift factorLift, ?_⟩, ?_⟩
  · exact congrArg Quiver.Hom.unop factorization
  · intro candidate candidateProperty
    apply Quiver.Hom.op_inj
    exact uniqueness candidate.op
      ⟨opLift candidateProperty.1, congrArg Quiver.Hom.op candidateProperty.2⟩

/-- Infinitesimal automorphisms of `Def_{X ⟶ Y}` at the trivial dual-number pushforward. -/
abbrev inf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) : Type u :=
  (Functor.infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X Y f hX hY hf)
    (trivialDeformation Λ k f hX hY hf) (trivialPushforward Λ k f hX hY hf) : Type u)

/-- The source automorphism of an infinitesimal automorphism of `f'`. -/
def infToSource {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (α : inf Λ k f hX hY hf) : FlatSchemeCat.inf Λ k X hX  :=
  let e : Aut (FlatSchemeCat.trivialObj Λ k X hX) :=
    (sourceFunctor Λ k).mapIso (fiberInclusion.mapIso α.val)
  let laws :
      (FlatSchemeCat.forget Λ k).IsHomLift (𝟙 (dualNumber Λ k)) e.hom ∧
      (∀ h : (FlatSchemeCat.forget Λ k).IsHomLift (𝟙 (dualNumber Λ k)) e.hom,
        Fiber.isoMk (x := FlatSchemeCat.trivialDeformation Λ k X hX)
          (y := FlatSchemeCat.trivialDeformation Λ k X hX) e h ∈ Functor.infinitesimalAutomorphismsAt
          (FlatSchemeCat.forget Λ k) (FlatSchemeCat.residueObj Λ k X hX)
          (FlatSchemeCat.trivialDeformation Λ k X hX)
          (FlatSchemeCat.trivialPushforward Λ k X hX)) := by
    constructor
    · apply IsHomLift.of_fac _ _ _ rfl rfl
      change 𝟙 (dualNumber Λ k) = (forget Λ k).map (fiberInclusion.map α.val.hom)
      exact @IsHomLift.eq_of_isHomLift _ _ _ _ (forget Λ k)
        (trivialObj Λ k f hX hY hf) (trivialObj Λ k f hX hY hf)
        (𝟙 _) (fiberInclusion.map α.val.hom) α.val.hom.property
    · intro h
      exact BasedFunctor.infAutMap_mem (p := forget Λ k) (q := FlatSchemeCat.forget Λ k)
        (BasedFunctor.ofFunctor (sourceFunctor Λ k) (by rfl))
        (trivialPushforward Λ k f hX hY hf) α
  ⟨Fiber.isoMk (x := FlatSchemeCat.trivialDeformation Λ k X hX)
          (y := FlatSchemeCat.trivialDeformation Λ k X hX) e laws.1, laws.2 laws.1⟩

/-- The target automorphism of an infinitesimal automorphism of `f'`. -/
def infToTarget {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (α : inf Λ k f hX hY hf) : FlatSchemeCat.inf Λ k Y hY  :=
  let e : Aut (FlatSchemeCat.trivialObj Λ k Y hY) :=
    (targetFunctor Λ k).mapIso (fiberInclusion.mapIso α.val)
  let laws :
      (FlatSchemeCat.forget Λ k).IsHomLift (𝟙 (dualNumber Λ k)) e.hom ∧
      (∀ h : (FlatSchemeCat.forget Λ k).IsHomLift (𝟙 (dualNumber Λ k)) e.hom,
        Fiber.isoMk (x := FlatSchemeCat.trivialDeformation Λ k Y hY)
          (y := FlatSchemeCat.trivialDeformation Λ k Y hY) e h ∈ Functor.infinitesimalAutomorphismsAt
          (FlatSchemeCat.forget Λ k) (FlatSchemeCat.residueObj Λ k Y hY)
          (FlatSchemeCat.trivialDeformation Λ k Y hY)
          (FlatSchemeCat.trivialPushforward Λ k Y hY)) := by
    constructor
    · apply IsHomLift.of_fac _ _ _ rfl rfl
      change 𝟙 (dualNumber Λ k) = (forget Λ k).map (fiberInclusion.map α.val.hom)
      exact @IsHomLift.eq_of_isHomLift _ _ _ _ (forget Λ k)
        (trivialObj Λ k f hX hY hf) (trivialObj Λ k f hX hY hf)
        (𝟙 _) (fiberInclusion.map α.val.hom) α.val.hom.property
    · intro h
      exact BasedFunctor.infAutMap_mem (p := forget Λ k) (q := FlatSchemeCat.forget Λ k)
        (BasedFunctor.ofFunctor (targetFunctor Λ k) (by rfl))
        (trivialPushforward Λ k f hX hY hf) α
  ⟨Fiber.isoMk (x := FlatSchemeCat.trivialDeformation Λ k Y hY)
          (y := FlatSchemeCat.trivialDeformation Λ k Y hY) e laws.1, laws.2 laws.1⟩

/-- The forgetful map `Inf(Def_{X ⟶ Y}) ⟶ Inf(Def_X) × Inf(Def_Y)`. -/
def infToProdInf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    inf Λ k f hX hY hf →ₗ[k] (FlatSchemeCat.inf Λ k X hX × FlatSchemeCat.inf Λ k Y hY)  :=
  let g := fun α ↦ (infToSource Λ k f hX hY hf α, infToTarget Λ k f hX hY hf α)
  let laws : IsLinearMap k g := by
    have hs := BasedFunctor.isLinearMap_infAutMap (p := forget Λ k) (q := FlatSchemeCat.forget Λ k)
      (BasedFunctor.ofFunctor (sourceFunctor Λ k) (by rfl))
      (trivialPushforward Λ k f hX hY hf)
    have ht := BasedFunctor.isLinearMap_infAutMap (p := forget Λ k) (q := FlatSchemeCat.forget Λ k)
      (BasedFunctor.ofFunctor (targetFunctor Λ k) (by rfl))
      (trivialPushforward Λ k f hX hY hf)
    exact ⟨fun α β ↦ Prod.ext (hs.map_add α β) (ht.map_add α β),
      fun c α ↦ Prod.ext (hs.map_smul c α) (ht.map_smul c α)⟩
  IsLinearMap.mk' g laws

/-- `infToProdInf` sends an automorphism of `f'` to the pair of source and target
automorphisms. -/
theorem infToProdInf_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (α : inf Λ k f hX hY hf) :
    infToProdInf Λ k f hX hY hf α =
      (infToSource Λ k f hX hY hf α, infToTarget Λ k f hX hY hf α) := rfl

/-- The tangent space `T Def_{X ⟶ Y}` is the tangent space of the residue-fibre slice. -/
abbrev tangentSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :=
  Functor.tangentSpaceAt (forget Λ k) (residueObj Λ k X Y f hX hY hf)

/-- The forgetful map `T Def_{X ⟶ Y} ⟶ T Def_X × T Def_Y`. -/
def tangentToProdTangent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX) :
    tangentSpace Λ k f hX hY hf →ₗ[k] (FlatSchemeCat.tangentSpace Λ k X hX × FlatSchemeCat.tangentSpace Λ k Y hY)  :=
  (BasedFunctor.differentialLinearMap (sourceBasedFunctor Λ k X Y f hX hY hf)).prod
    (BasedFunctor.differentialLinearMap (targetBasedFunctor Λ k X Y f hX hY hf))

/-- `tangentToProdTangent` on a represented class is the pair of forgotten classes. -/
theorem tangentToProdTangent_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    (x : (deformationForget Λ k X Y f hX hY hf).Fiber (dualNumber Λ k)) :
    tangentToProdTangent Λ k f hX hY hf (Functor.tangentSpace.mk (deformationForget Λ k X Y f hX hY hf) x) =
      (Functor.tangentSpace.mk (FlatSchemeCat.deformationForget Λ k X hX)
        (((sourceBasedFunctor Λ k X Y f hX hY hf).fiberFunctor (dualNumber Λ k)).obj x),
        Functor.tangentSpace.mk (FlatSchemeCat.deformationForget Λ k Y hY)
        (((targetBasedFunctor Λ k X Y f hX hY hf).fiberFunctor (dualNumber Λ k)).obj x)) :=
  rfl

end FlatSchemeMorphismCat
