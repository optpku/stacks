module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap90.Definition_90_19_2
public import stacks_project.Chap90.Definition_90_19_5_AutFunctor
public import stacks_project.Chap90.Lemma_90_16_6
public import stacks_project.Chap90.Lemma_90_19_9_Module
public import stacks_project.Chap90.Remark_90_12_5_TangentSpace
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass
public import stacks_project.Chap93.Example_93_9_1_Schemes_Deformation
public import stacks_project.Chap93.Example_93_10_1_Morphisms_of_schemes_Category
public import stacks_project.Chap93.Lemma_93_9_2
public import stacks_project.Chap93.Lemma_93_10_2_RimSchlessinger

/-!
# Trivial dual-number lifts, Inf, and tangent spaces of `Def_{X ⟶ Y}`

The forgetful functors `Def_{X ⟶ Y} ⥤ Def_X` and `Def_{X ⟶ Y} ⥤ Def_Y` induce the
outer maps of Lemma 93.10.3. Infinitesimal automorphisms are taken at the trivial
dual-number pushforward; the tangent space is the type of isomorphism classes of
the same dual-number fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open Functor.Fiber
open ArtinianLocalAlgCat
open scoped DualNumber

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeCat

/-- The trivial dual-number scheme `X ×_{Spec k} Spec k[ε]`. -/
def trivialScheme (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) : Scheme.{u} :=
  pullback hX (specMap (residueToDualNumber Λ k))

/-- `trivialScheme` is the pullback of `hX` along `Spec k[ε] ⟶ Spec k`. -/
theorem trivialScheme_eq (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    trivialScheme Λ k X hX = pullback hX (specMap (residueToDualNumber Λ k)) := sorry

/-- The structure morphism of the trivial dual-number scheme over `Spec k[ε]`. -/
def trivialSchemeOver (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    trivialScheme Λ k X hX ⟶ Spec (CommRingCat.of (dualNumber Λ k).carrier) :=
  pullback.snd hX (specMap (residueToDualNumber Λ k))

/-- The projection `X' ⟶ X` of the trivial dual-number thickening. -/
def trivialSchemeProj (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    trivialScheme Λ k X hX ⟶ X :=
  pullback.fst hX (specMap (residueToDualNumber Λ k))

/-- The closed immersion of `X` into the trivial dual-number thickening. -/
def trivialSchemeImmersion (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    X ⟶ trivialScheme Λ k X hX :=
  pullback.lift (𝟙 X) (hX ≫ specMap (dualNumberToResidue Λ k)) sorry

/-- `trivialSchemeImmersion` is the section of `trivialSchemeProj` induced by `k[ε] ⟶ k`. -/
theorem trivialSchemeImmersion_comp_proj (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) :
    trivialSchemeImmersion Λ k X hX ≫ trivialSchemeProj Λ k X hX = 𝟙 X := sorry

/-- Base change of a flat morphism along `Spec k[ε] ⟶ Spec k` remains flat. -/
instance instFlat_trivialSchemeOver (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    AlgebraicGeometry.Flat (trivialSchemeOver Λ k X hX) := sorry

/-- The trivial dual-number object `(k[ε], X')` of `FlatSchemeCat`. -/
def trivialObj (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] : FlatSchemeCat Λ k :=
  of (dualNumber Λ k) (trivialScheme Λ k X hX) (trivialSchemeOver Λ k X hX)

/-- The base of `trivialObj` is `k[ε]`. -/
theorem trivialObj_base (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    (trivialObj Λ k X hX).base = dualNumber Λ k := sorry

/-- Residue object `x0 = (k, X)` with structure morphism valued in `Spec k`. -/
def ofResidueK (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [hflat : AlgebraicGeometry.Flat hX] : FlatSchemeCat Λ k where
  base := residue Λ k
  scheme := X
  structureHom := hX
  isFlat := hflat

/-- `x0 = (k, X)` as an object of the residue fibre of `forget`. -/
def residueObjK (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    (forget Λ k).Fiber (residue Λ k) :=
  Fiber.mk (rfl : (forget Λ k).obj (ofResidueK Λ k X hX) = residue Λ k)

/-- The trivial dual-number deformation of `x0 = (k, X)` in the fibre of `forget`. -/
def trivialDeformation (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    (forget Λ k).Fiber (dualNumber Λ k) :=
  Fiber.mk (rfl : (forget Λ k).obj (trivialObj Λ k X hX) = dualNumber Λ k)

/-- The underlying object of `trivialDeformation` is `trivialObj`. -/
theorem trivialDeformation_obj (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    fiberInclusion.obj (trivialDeformation Λ k X hX) = trivialObj Λ k X hX := sorry

/-- The canonical strongly cocartesian pushforward of `x0` along `k ⟶ k[ε]`. -/
def trivialPushforward (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    fiberInclusion.obj (residueObjK Λ k X hX) ⟶
      fiberInclusion.obj (trivialDeformation Λ k X hX) :=
  Hom.of (residueToDualNumber Λ k) (trivialSchemeProj Λ k X hX) sorry

/-- The base map of `trivialPushforward` is `residueToDualNumber`. -/
theorem trivialPushforward_base (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    (forget Λ k).map (trivialPushforward Λ k X hX) = residueToDualNumber Λ k := sorry

/-- The canonical pushforward of `x0` along `k ⟶ k[ε]` is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward
    (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    (forget Λ k).IsStronglyCocartesian (residueToDualNumber Λ k)
      (trivialPushforward Λ k X hX) := sorry

/-- Infinitesimal automorphisms of `Def_X` at the trivial dual-number pushforward. -/
abbrev inf (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] : Type u :=
  (Functor.infinitesimalAutomorphismsAt (forget Λ k) (residueObjK Λ k X hX)
    (trivialDeformation Λ k X hX) (trivialPushforward Λ k X hX) : Type u)

/-- Membership in `inf` is the equalizer condition along the unique retraction of the
chosen dual-number pushforward. -/
theorem mem_inf (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] (α : Aut (trivialDeformation Λ k X hX)) :
    α ∈ Functor.infinitesimalAutomorphismsAt (forget Λ k) (residueObjK Λ k X hX)
      (trivialDeformation Λ k X hX) (trivialPushforward Λ k X hX) ↔
      fiberInclusion.map α.hom ≫ retraction (forget Λ k) (trivialPushforward Λ k X hX) =
        retraction (forget Λ k) (trivialPushforward Λ k X hX) := sorry

/-- Additive structure on `Inf(Def_X)` from Lemma 90.19.9. -/
instance instAddCommGroup_inf (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] : AddCommGroup (inf Λ k X hX) :=
  instAddCommGroup_infinitesimalAutomorphismsAt (forget Λ k) (residueObjK Λ k X hX)
    (trivialDeformation Λ k X hX) (trivialPushforward Λ k X hX)

/-- `k`-vector space structure on `Inf(Def_X)` from Lemma 90.19.9. -/
instance instModule_inf (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] : Module k (inf Λ k X hX) :=
  instModule_infinitesimalAutomorphismsAt (forget Λ k) (residueObjK Λ k X hX)
    (trivialDeformation Λ k X hX) (trivialPushforward Λ k X hX)

/-- The slice projection of `Def_X` to `C_Λ`. -/
abbrev deformationForget (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    Over (fiberInclusion.obj (residueObjK Λ k X hX)) ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (fiberInclusion.obj (residueObjK Λ k X hX)) ⋙ forget Λ k

/-- `deformationForget` is the composite of the Over-forgetful functor with `forget`. -/
theorem deformationForget_eq (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    deformationForget Λ k X hX =
      Over.forget (fiberInclusion.obj (residueObjK Λ k X hX)) ⋙ forget Λ k := sorry

/-- The slice projection of `Def_X` is a predeformation category. -/
instance instIsPredeformationCategory_deformationForget
    (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    IsPredeformationCategory (deformationForget Λ k X hX) :=
  instIsPredeformationCategory_overForget (forget Λ k) (residueObjK Λ k X hX)

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationForget_op
    (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    IsFibered.InGroupoids (deformationForget Λ k X hX).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- The isomorphism-class functor of `Def_X` satisfies Schlessinger's (H2). -/
instance instHasSchlessingerH2_fiberIsoClass_deformationForget
    (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    HasSchlessingerH2 (fiberIsoClassFunctor (deformationForget Λ k X hX)) :=
  instHasSchlessingerH2_fiberIsoClass_sliceAt (forget Λ k) (residueObjK Λ k X hX)

/-- The tangent space `T Def_X` is the tangent space of the residue-fibre slice. -/
abbrev tangentSpace (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :=
  (fiberIsoClassFunctor (deformationForget Λ k X hX)).obj (dualNumber Λ k)

/-- Unfolding of `tangentSpace`. -/
theorem tangentSpace_def (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    tangentSpace Λ k X hX =
      (fiberIsoClassFunctor (deformationForget Λ k X hX)).obj (dualNumber Λ k) := sorry

/-- Additive group structure on `T Def_X` from Lemma 90.12.2. -/
instance instAddCommGroup_tangentSpace (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Flat hX] :
    AddCommGroup (tangentSpace Λ k X hX) :=
  instAddCommGroup_fiberDualTangent (deformationForget Λ k X hX)

/-- `T Def_X` is a `k`-vector space, with scalars acting by dual-number pushforward. -/
instance instModule_tangentSpace (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Flat hX] :
    Module k (tangentSpace Λ k X hX) :=
  instModule_fiberDualTangent (deformationForget Λ k X hX)


/-- The isomorphism class of a dual-number lift of `X`. -/
def tangentSpaceMk (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    tangentSpace Λ k X hX :=
  Quotient.mk'' x

/-- `tangentSpaceMk` is the class of the given dual-number fibre object. -/
theorem tangentSpaceMk_eq (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x : (deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    tangentSpaceMk Λ k X hX x = Quotient.mk'' x := sorry

/-- Two dual-number lifts determine the same tangent vector if and only if they are isomorphic. -/
theorem tangentSpaceMk_eq_mk (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX]
    (x y : (deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    tangentSpaceMk Λ k X hX x = tangentSpaceMk Λ k X hX y ↔ Nonempty (x ≅ y) := sorry

/-- The unique retraction of the trivial dual-number pushforward, as a morphism of `Def_X`. -/
def trivialLiftHom (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    trivialObj Λ k X hX ⟶ fiberInclusion.obj (residueObjK Λ k X hX) :=
  retraction (forget Λ k) (trivialPushforward Λ k X hX)

/-- The trivial dual-number lift of `X` in the slice `Def_X`. -/
def trivialLift (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    (deformationForget Λ k X hX).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k X hX).obj (Over.mk (trivialLiftHom Λ k X hX)) =
      dualNumber Λ k)

/-- The zero tangent vector of `Def_X`. -/
def trivialTangent (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] : tangentSpace Λ k X hX :=
  tangentSpaceMk Λ k X hX (trivialLift Λ k X hX)

/-- `trivialTangent` is the class of `trivialLift`. -/
theorem trivialTangent_spec (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Flat hX] :
    trivialTangent Λ k X hX = tangentSpaceMk Λ k X hX (trivialLift Λ k X hX) := sorry


end FlatSchemeCat

namespace FlatSchemeMorphismCat

/-- The trivial dual-number source scheme `X ×_{Spec k} Spec k[ε]`. -/
abbrev trivialSource (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) : Scheme.{u} :=
  FlatSchemeCat.trivialScheme Λ k X hX

/-- The trivial dual-number target scheme `Y ×_{Spec k} Spec k[ε]`. -/
abbrev trivialTarget (Y : Scheme.{u}) (hY : Y ⟶ Spec (CommRingCat.of k)) : Scheme.{u} :=
  FlatSchemeCat.trivialScheme Λ k Y hY

/-- The trivial dual-number morphism `f' = f × id : X' ⟶ Y'`. -/
def trivialHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k)) :
    trivialSource Λ k X hX ⟶ trivialTarget Λ k Y hY :=
  pullback.lift (FlatSchemeCat.trivialSchemeProj Λ k X hX ≫ f)
    (FlatSchemeCat.trivialSchemeOver Λ k X hX) sorry

/-- `trivialHom` is the unique map over `Spec k[ε]` lifting `f`. -/
theorem trivialHom_spec {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k)) :
    trivialHom Λ k f hX hY ≫ FlatSchemeCat.trivialSchemeProj Λ k Y hY =
      FlatSchemeCat.trivialSchemeProj Λ k X hX ≫ f := sorry

/-- The structure morphism of `X'` over `Spec k[ε]`. -/
abbrev trivialSourceOver (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k)) :
    trivialSource Λ k X hX ⟶ Spec (CommRingCat.of (dualNumber Λ k).carrier) :=
  FlatSchemeCat.trivialSchemeOver Λ k X hX

/-- The structure morphism of `Y'` over `Spec k[ε]`. -/
abbrev trivialTargetOver (Y : Scheme.{u}) (hY : Y ⟶ Spec (CommRingCat.of k)) :
    trivialTarget Λ k Y hY ⟶ Spec (CommRingCat.of (dualNumber Λ k).carrier) :=
  FlatSchemeCat.trivialSchemeOver Λ k Y hY

/-- The trivial dual-number object `(k[ε], X' ⟶ Y')` of `FlatSchemeMorphismCat`. -/
def trivialObj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    FlatSchemeMorphismCat Λ k :=
  of (dualNumber Λ k) (trivialSource Λ k X hX) (trivialTarget Λ k Y hY)
    (trivialHom Λ k f hX hY) (trivialSourceOver Λ k X hX) (trivialTargetOver Λ k Y hY) sorry

/-- The base of `trivialObj` is `k[ε]`. -/
theorem trivialObj_base {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    (trivialObj Λ k f hX hY hf).base = dualNumber Λ k := sorry

/-- The trivial dual-number deformation of `x0 = (k, X ⟶ Y)` in the fibre of `forget`. -/
def trivialDeformation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    (forget Λ k).Fiber (dualNumber Λ k) :=
  Fiber.mk (rfl : (forget Λ k).obj (trivialObj Λ k f hX hY hf) = dualNumber Λ k)

/-- The underlying object of `trivialDeformation` is `trivialObj`. -/
theorem trivialDeformation_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    fiberInclusion.obj (trivialDeformation Λ k f hX hY hf) =
      trivialObj Λ k f hX hY hf := sorry

/-- The canonical strongly cocartesian pushforward of `x0` along `k ⟶ k[ε]`. -/
def trivialPushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    fiberInclusion.obj (residueObj Λ k X Y f hX hY hf) ⟶
      fiberInclusion.obj (trivialDeformation Λ k f hX hY hf) :=
  Hom.of (residueToDualNumber Λ k)
    (FlatSchemeCat.trivialSchemeProj Λ k X hX)
    (FlatSchemeCat.trivialSchemeProj Λ k Y hY) sorry sorry

/-- The base map of `trivialPushforward` is `residueToDualNumber`. -/
theorem trivialPushforward_base {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    (forget Λ k).map (trivialPushforward Λ k f hX hY hf) =
      residueToDualNumber Λ k := sorry

/-- The canonical pushforward of `x0` along `k ⟶ k[ε]` is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    (forget Λ k).IsStronglyCocartesian (residueToDualNumber Λ k)
      (trivialPushforward Λ k f hX hY hf) := sorry

/-- Infinitesimal automorphisms of `Def_{X ⟶ Y}` at the trivial dual-number pushforward. -/
abbrev inf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] : Type u :=
  (Functor.infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X Y f hX hY hf)
    (trivialDeformation Λ k f hX hY hf) (trivialPushforward Λ k f hX hY hf) : Type u)

/-- Membership in `inf` is the equalizer condition along the unique retraction of the
chosen dual-number pushforward. -/
theorem mem_inf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (α : Aut (trivialDeformation Λ k f hX hY hf)) :
    α ∈ Functor.infinitesimalAutomorphismsAt (forget Λ k)
        (residueObj Λ k X Y f hX hY hf) (trivialDeformation Λ k f hX hY hf)
        (trivialPushforward Λ k f hX hY hf) ↔
      fiberInclusion.map α.hom ≫
          retraction (forget Λ k) (trivialPushforward Λ k f hX hY hf) =
        retraction (forget Λ k) (trivialPushforward Λ k f hX hY hf) := sorry

/-- Additive structure on `Inf(Def_{X ⟶ Y})` from Lemma 90.19.9. -/
instance instAddCommGroup_inf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    AddCommGroup (inf Λ k f hX hY hf) :=
  instAddCommGroup_infinitesimalAutomorphismsAt (forget Λ k)
    (residueObj Λ k X Y f hX hY hf) (trivialDeformation Λ k f hX hY hf)
    (trivialPushforward Λ k f hX hY hf)

/-- `k`-vector space structure on `Inf(Def_{X ⟶ Y})` from Lemma 90.19.9. -/
instance instModule_inf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    Module k (inf Λ k f hX hY hf) :=
  instModule_infinitesimalAutomorphismsAt (forget Λ k)
    (residueObj Λ k X Y f hX hY hf) (trivialDeformation Λ k f hX hY hf)
    (trivialPushforward Λ k f hX hY hf)

/-- Send a pair `(A, X ⟶ Y)` to the source pair `(A, X)`. -/
def toSourceObj (P : FlatSchemeMorphismCat Λ k) : FlatSchemeCat Λ k :=
  FlatSchemeCat.of P.base P.source P.sourceOver

/-- Send a morphism of pairs to the induced morphism of source schemes. -/
def toSourceMap {src tgt : FlatSchemeMorphismCat Λ k} (φ : src ⟶ tgt) :
    toSourceObj Λ k src ⟶ toSourceObj Λ k tgt :=
  FlatSchemeCat.Hom.of φ.base φ.sourceMap sorry

/-- The forgetful functor `F ⥤ FlatSchemeCat` on source schemes. -/
def toSource : FlatSchemeMorphismCat Λ k ⥤ FlatSchemeCat Λ k where
  obj := toSourceObj Λ k
  map := toSourceMap Λ k
  map_id := sorry
  map_comp := sorry

/-- `toSource` evaluates to the stored source scheme. -/
theorem toSource_obj (P : FlatSchemeMorphismCat Λ k) :
    (toSource Λ k).obj P = toSourceObj Λ k P := sorry

/-- Send a pair `(A, X ⟶ Y)` to the target pair `(A, Y)`. -/
def toTargetObj (P : FlatSchemeMorphismCat Λ k) : FlatSchemeCat Λ k :=
  FlatSchemeCat.of P.base P.target P.targetOver

/-- Send a morphism of pairs to the induced morphism of target schemes. -/
def toTargetMap {src tgt : FlatSchemeMorphismCat Λ k} (φ : src ⟶ tgt) :
    toTargetObj Λ k src ⟶ toTargetObj Λ k tgt :=
  FlatSchemeCat.Hom.of φ.base φ.targetMap sorry

/-- The forgetful functor `F ⥤ FlatSchemeCat` on target schemes. -/
def toTarget : FlatSchemeMorphismCat Λ k ⥤ FlatSchemeCat Λ k where
  obj := toTargetObj Λ k
  map := toTargetMap Λ k
  map_id := sorry
  map_comp := sorry

/-- `toTarget` evaluates to the stored target scheme. -/
theorem toTarget_obj (P : FlatSchemeMorphismCat Λ k) :
    (toTarget Λ k).obj P = toTargetObj Λ k P := sorry

/-- The source component of a slice arrow of `Def_{X ⟶ Y}`, as a morphism of `Def_X`. -/
def forgetToSourceHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (ξ : deformation Λ k X Y f hX hY hf) :
    toSourceObj Λ k ξ.left ⟶
      fiberInclusion.obj (FlatSchemeCat.residueObjK Λ k X hX) :=
  FlatSchemeCat.Hom.of
    (ξ.hom.base ≫
      eqToHom
        (rfl : (fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)).base = residue Λ k))
    (eqToHom
        (rfl : X = (fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)).source) ≫
      ξ.hom.sourceMap) sorry

/-- The target component of a slice arrow of `Def_{X ⟶ Y}`, as a morphism of `Def_Y`. -/
def forgetToTargetHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (ξ : deformation Λ k X Y f hX hY hf) :
    toTargetObj Λ k ξ.left ⟶
      fiberInclusion.obj (FlatSchemeCat.residueObjK Λ k Y hY) :=
  FlatSchemeCat.Hom.of
    (ξ.hom.base ≫
      eqToHom
        (rfl : (fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)).base = residue Λ k))
    (eqToHom
        (rfl : Y = (fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)).target) ≫
      ξ.hom.targetMap) sorry

/-- The forgetful functor `Def_{X ⟶ Y} ⥤ Def_X`. -/
def forgetToSource {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    deformation Λ k X Y f hX hY hf ⥤
      Over (fiberInclusion.obj (FlatSchemeCat.residueObjK Λ k X hX)) where
  obj ξ := Over.mk (forgetToSourceHom Λ k f hX hY hf ξ)
  map φ := Over.homMk (toSourceMap Λ k φ.left) sorry
  map_id := sorry
  map_comp := sorry

/-- `forgetToSource` commutes with the projections to `C_Λ`. -/
theorem forgetToSource_comp_forget {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    forgetToSource Λ k f hX hY hf ⋙ FlatSchemeCat.deformationForget Λ k X hX =
      Over.forget (fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙ forget Λ k :=
  sorry

/-- The forgetful functor `Def_{X ⟶ Y} ⥤ Def_Y`. -/
def forgetToTarget {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    deformation Λ k X Y f hX hY hf ⥤
      Over (fiberInclusion.obj (FlatSchemeCat.residueObjK Λ k Y hY)) where
  obj ξ := Over.mk (forgetToTargetHom Λ k f hX hY hf ξ)
  map φ := Over.homMk (toTargetMap Λ k φ.left) sorry
  map_id := sorry
  map_comp := sorry

/-- `forgetToTarget` commutes with the projections to `C_Λ`. -/
theorem forgetToTarget_comp_forget {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    forgetToTarget Λ k f hX hY hf ⋙ FlatSchemeCat.deformationForget Λ k Y hY =
      Over.forget (fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙ forget Λ k :=
  sorry

/-- The source automorphism of an infinitesimal automorphism of `f'`. -/
def infToSource {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (α : inf Λ k f hX hY hf) : FlatSchemeCat.inf Λ k X hX :=
  ⟨Fiber.isoMk
      { hom :=
          FlatSchemeCat.Hom.of (𝟙 (dualNumber Λ k))
            (fiberInclusion.map α.val.hom).sourceMap sorry
        inv :=
          FlatSchemeCat.Hom.of (𝟙 (dualNumber Λ k))
            (fiberInclusion.map α.val.inv).sourceMap sorry
        hom_inv_id := sorry
        inv_hom_id := sorry }
      sorry,
    sorry⟩

/-- The target automorphism of an infinitesimal automorphism of `f'`. -/
def infToTarget {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (α : inf Λ k f hX hY hf) : FlatSchemeCat.inf Λ k Y hY :=
  ⟨Fiber.isoMk
      { hom :=
          FlatSchemeCat.Hom.of (𝟙 (dualNumber Λ k))
            (fiberInclusion.map α.val.hom).targetMap sorry
        inv :=
          FlatSchemeCat.Hom.of (𝟙 (dualNumber Λ k))
            (fiberInclusion.map α.val.inv).targetMap sorry
        hom_inv_id := sorry
        inv_hom_id := sorry }
      sorry,
    sorry⟩

/-- The product of infinitesimal automorphism spaces of `Def_X` and `Def_Y`. -/
abbrev prodInf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] : Type u :=
  FlatSchemeCat.inf Λ k X hX × FlatSchemeCat.inf Λ k Y hY

/-- `Inf(Def_X × Def_Y)` is the product of `Inf(Def_X)` and `Inf(Def_Y)`. -/
theorem inf_prod_spec {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    prodInf Λ k f hX hY hf =
      (FlatSchemeCat.inf Λ k X hX × FlatSchemeCat.inf Λ k Y hY) := sorry

/-- The forgetful map `Inf(Def_{X ⟶ Y}) ⟶ Inf(Def_X) × Inf(Def_Y)`. -/
def infToProdInf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    inf Λ k f hX hY hf →ₗ[k] prodInf Λ k f hX hY hf where
  toFun α := (infToSource Λ k f hX hY hf α, infToTarget Λ k f hX hY hf α)
  map_add' := sorry
  map_smul' := sorry

/-- `infToProdInf` sends an automorphism of `f'` to the pair of source and target
automorphisms. -/
theorem infToProdInf_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (α : inf Λ k f hX hY hf) :
    infToProdInf Λ k f hX hY hf α =
      (infToSource Λ k f hX hY hf α, infToTarget Λ k f hX hY hf α) := sorry

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationForget_op {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    IsFibered.InGroupoids (deformationForget Λ k X Y f hX hY hf).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- The isomorphism-class functor of `Def_{X ⟶ Y}` satisfies Schlessinger's (H2). -/
instance instHasSchlessingerH2_fiberIsoClass_deformationForget {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    HasSchlessingerH2
      (fiberIsoClassFunctor (deformationForget Λ k X Y f hX hY hf)) :=
  instHasSchlessingerH2_fiberIsoClass_sliceAt (forget Λ k)
    (residueObj Λ k X Y f hX hY hf)

/-- The tangent space `T Def_{X ⟶ Y}` is the tangent space of the residue-fibre slice. -/
abbrev tangentSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :=
  (fiberIsoClassFunctor (deformationForget Λ k X Y f hX hY hf)).obj (dualNumber Λ k)

/-- Unfolding of `tangentSpace`. -/
theorem tangentSpace_def {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    tangentSpace Λ k f hX hY hf =
      (fiberIsoClassFunctor (deformationForget Λ k X Y f hX hY hf)).obj
        (dualNumber Λ k) := sorry

/-- The isomorphism class of a dual-number lift of `X ⟶ Y`. -/
def tangentSpaceMk {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (x : (deformationForget Λ k X Y f hX hY hf).Fiber (dualNumber Λ k)) :
    tangentSpace Λ k f hX hY hf :=
  Quotient.mk'' x

/-- `tangentSpaceMk` is the class of the given dual-number fibre object. -/
theorem tangentSpaceMk_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (x : (deformationForget Λ k X Y f hX hY hf).Fiber (dualNumber Λ k)) :
    tangentSpaceMk Λ k f hX hY hf x = Quotient.mk'' x := sorry

/-- Two dual-number lifts determine the same tangent vector iff they are isomorphic. -/
theorem tangentSpaceMk_eq_mk {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (x y : (deformationForget Λ k X Y f hX hY hf).Fiber (dualNumber Λ k)) :
    tangentSpaceMk Λ k f hX hY hf x = tangentSpaceMk Λ k f hX hY hf y ↔
      Nonempty (x ≅ y) := sorry

/-- The unique retraction of the trivial dual-number pushforward in `Def_{X ⟶ Y}`. -/
def trivialLiftHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    trivialObj Λ k f hX hY hf ⟶
      fiberInclusion.obj (residueObj Λ k X Y f hX hY hf) :=
  retraction (forget Λ k) (trivialPushforward Λ k f hX hY hf)

/-- The trivial dual-number lift of `X ⟶ Y` in the slice `Def_{X ⟶ Y}`. -/
def trivialLift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    (deformationForget Λ k X Y f hX hY hf).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k X Y f hX hY hf).obj (Over.mk (trivialLiftHom Λ k f hX hY hf)) =
      dualNumber Λ k)

/-- The zero tangent vector of `Def_{X ⟶ Y}`. -/
def trivialTangent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    tangentSpace Λ k f hX hY hf :=
  tangentSpaceMk Λ k f hX hY hf (trivialLift Λ k f hX hY hf)

/-- `trivialTangent` is the class of `trivialLift`. -/
theorem trivialTangent_spec {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    trivialTangent Λ k f hX hY hf =
      tangentSpaceMk Λ k f hX hY hf (trivialLift Λ k f hX hY hf) := sorry


/-- Additive group structure on `T Def_{X ⟶ Y}` from Lemma 90.12.2. -/
instance instAddCommGroup_tangentSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    AddCommGroup (tangentSpace Λ k f hX hY hf) :=
  instAddCommGroup_fiberDualTangent (deformationForget Λ k X Y f hX hY hf)

/-- `T Def_{X ⟶ Y}` is a `k`-vector space. -/
instance instModule_tangentSpace {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    Module k (tangentSpace Λ k f hX hY hf) :=
  instModule_fiberDualTangent (deformationForget Λ k X Y f hX hY hf)

/-- The product of tangent spaces of `Def_X` and `Def_Y`. -/
abbrev prodTangent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :=
  FlatSchemeCat.tangentSpace Λ k X hX × FlatSchemeCat.tangentSpace Λ k Y hY

/-- `T(Def_X × Def_Y)` is the product of the scheme-level tangent spaces. -/
theorem prodTangent_def {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    prodTangent Λ k f hX hY hf =
      (FlatSchemeCat.tangentSpace Λ k X hX × FlatSchemeCat.tangentSpace Λ k Y hY) := sorry

/-- Forget a dual-number lift of `X ⟶ Y` to a dual-number lift of `X`. -/
def forgetToSourceFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (x : (deformationForget Λ k X Y f hX hY hf).Fiber (dualNumber Λ k)) :
    (FlatSchemeCat.deformationForget Λ k X hX).Fiber (dualNumber Λ k) :=
  ⟨(forgetToSource Λ k f hX hY hf).obj (fiberInclusion.obj x), sorry⟩

/-- Forget a dual-number lift of `X ⟶ Y` to a dual-number lift of `Y`. -/
def forgetToTargetFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (x : (deformationForget Λ k X Y f hX hY hf).Fiber (dualNumber Λ k)) :
    (FlatSchemeCat.deformationForget Λ k Y hY).Fiber (dualNumber Λ k) :=
  ⟨(forgetToTarget Λ k f hX hY hf).obj (fiberInclusion.obj x), sorry⟩

/-- The forgetful map `T Def_{X ⟶ Y} ⟶ T Def_X × T Def_Y`. -/
def tangentToProdTangent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    tangentSpace Λ k f hX hY hf →ₗ[k] prodTangent Λ k f hX hY hf where
  toFun :=
    Quotient.lift
      (fun x ↦
        (FlatSchemeCat.tangentSpaceMk Λ k X hX (forgetToSourceFiber Λ k f hX hY hf x),
          FlatSchemeCat.tangentSpaceMk Λ k Y hY (forgetToTargetFiber Λ k f hX hY hf x)))
      (fun _ _ _ ↦ sorry)
  map_add' := sorry
  map_smul' := sorry

/-- `tangentToProdTangent` on a represented class is the pair of forgotten classes. -/
theorem tangentToProdTangent_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY]
    (x : (deformationForget Λ k X Y f hX hY hf).Fiber (dualNumber Λ k)) :
    tangentToProdTangent Λ k f hX hY hf (tangentSpaceMk Λ k f hX hY hf x) =
      (FlatSchemeCat.tangentSpaceMk Λ k X hX (forgetToSourceFiber Λ k f hX hY hf x),
        FlatSchemeCat.tangentSpaceMk Λ k Y hY (forgetToTargetFiber Λ k f hX hY hf x)) :=
  sorry

end FlatSchemeMorphismCat
