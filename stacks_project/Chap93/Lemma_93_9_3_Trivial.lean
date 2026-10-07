module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap90.Definition_90_19_2
public import stacks_project.Chap90.Lemma_90_16_6
public import stacks_project.Chap90.Lemma_90_19_9_Module
public import stacks_project.Chap90.Remark_90_12_5_TangentSpace
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass
public import stacks_project.Chap93.Example_93_9_1_Schemes_Deformation
public import stacks_project.Chap93.Lemma_93_9_2

/-!
# Trivial dual-number lift, Inf, and tangent space of `Def_X`

The trivial deformation `X' = X ×_{Spec k} Spec k[ε]` of a scheme over `k`,
together with `Inf(Def_X)` at this pushforward and `T Def_X`.
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
def trivialScheme (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) : Scheme.{u} :=
  pullback hX (specMap (residueToDualNumber Λ k))

/-- `trivialScheme` is the pullback of `hX` along `Spec k[ε] ⟶ Spec k`. -/
theorem trivialScheme_eq (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :
    trivialScheme Λ k X hX = pullback hX (specMap (residueToDualNumber Λ k)) := sorry

/-- The structure morphism of the trivial dual-number scheme over `Spec k[ε]`. -/
def trivialSchemeOver (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :
    trivialScheme Λ k X hX ⟶ Spec (CommRingCat.of (dualNumber Λ k).carrier) :=
  pullback.snd hX (specMap (residueToDualNumber Λ k))

/-- The projection `X' ⟶ X` of the trivial dual-number thickening. -/
def trivialSchemeProj (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :
    trivialScheme Λ k X hX ⟶ X :=
  pullback.fst hX (specMap (residueToDualNumber Λ k))

/-- The closed immersion of `X` into the trivial dual-number thickening. -/
def trivialSchemeImmersion (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :
    X ⟶ trivialScheme Λ k X hX :=
  pullback.lift (𝟙 X) (hX ≫ specMap (dualNumberToResidue Λ k)) sorry

/-- `trivialSchemeImmersion` is the section of `trivialSchemeProj` induced by `k[ε] ⟶ k`. -/
theorem trivialSchemeImmersion_comp_proj (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier)) :
    trivialSchemeImmersion Λ k X hX ≫ trivialSchemeProj Λ k X hX = 𝟙 X := sorry

/-- Base change of a flat morphism along `Spec k[ε] ⟶ Spec k` remains flat. -/
instance instFlat_trivialSchemeOver (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    AlgebraicGeometry.Flat (trivialSchemeOver Λ k X hX) := sorry

/-- The trivial dual-number object `(k[ε], X')` of `FlatSchemeCat`. -/
def trivialObj (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] : FlatSchemeCat Λ k :=
  of (dualNumber Λ k) (trivialScheme Λ k X hX) (trivialSchemeOver Λ k X hX)

/-- The base of `trivialObj` is `k[ε]`. -/
theorem trivialObj_base (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    (trivialObj Λ k X hX).base = dualNumber Λ k := sorry

/-- The trivial dual-number deformation of `x0 = (k, X)` in the fibre of `forget`. -/
def trivialDeformation (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    (forget Λ k).Fiber (dualNumber Λ k) :=
  Fiber.mk (rfl : (forget Λ k).obj (trivialObj Λ k X hX) = dualNumber Λ k)

/-- The underlying object of `trivialDeformation` is `trivialObj`. -/
theorem trivialDeformation_obj (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    fiberInclusion.obj (trivialDeformation Λ k X hX) = trivialObj Λ k X hX := sorry

/-- The canonical strongly cocartesian pushforward of `x0` along `k ⟶ k[ε]`. -/
def trivialPushforward (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    fiberInclusion.obj (residueObj Λ k X hX) ⟶
      fiberInclusion.obj (trivialDeformation Λ k X hX) :=
  Hom.of (residueToDualNumber Λ k) (trivialSchemeProj Λ k X hX)
    (IsPullback.of_hasPullback hX (specMap (residueToDualNumber Λ k)))

/-- The base map of `trivialPushforward` is `residueToDualNumber`. -/
theorem trivialPushforward_base (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    (forget Λ k).map (trivialPushforward Λ k X hX) = residueToDualNumber Λ k := sorry

/-- The canonical pushforward of `x0` along `k ⟶ k[ε]` is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    (forget Λ k).IsStronglyCocartesian (residueToDualNumber Λ k)
      (trivialPushforward Λ k X hX) := sorry

/-- Infinitesimal automorphisms of `Def_X` at the trivial dual-number pushforward. -/
abbrev inf (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] : Type u :=
  (Functor.infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X hX)
    (trivialDeformation Λ k X hX) (trivialPushforward Λ k X hX) : Type u)

/-- Unfolding of `inf`. -/
theorem inf_def (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    inf Λ k X hX =
      (Functor.infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X hX)
        (trivialDeformation Λ k X hX) (trivialPushforward Λ k X hX) : Type u) := sorry

/-- Membership in `inf` is the equalizer condition along the unique retraction of the
chosen dual-number pushforward. -/
theorem mem_inf (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] (α : Aut (trivialDeformation Λ k X hX)) :
    α ∈ Functor.infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X hX)
      (trivialDeformation Λ k X hX) (trivialPushforward Λ k X hX) ↔
      fiberInclusion.map α.hom ≫ retraction (forget Λ k) (trivialPushforward Λ k X hX) =
        retraction (forget Λ k) (trivialPushforward Λ k X hX) := sorry

/-- Additive structure on `Inf(Def_X)` from Lemma 90.19.9. -/
instance instAddCommGroup_inf (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] : AddCommGroup (inf Λ k X hX) :=
  instAddCommGroup_infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X hX)
    (trivialDeformation Λ k X hX) (trivialPushforward Λ k X hX)

/-- `k`-vector space structure on `Inf(Def_X)` from Lemma 90.19.9. -/
instance instModule_inf (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] : Module k (inf Λ k X hX) :=
  instModule_infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X hX)
    (trivialDeformation Λ k X hX) (trivialPushforward Λ k X hX)

/-- The slice projection of `Def_X` to `C_Λ`. -/
abbrev deformationForget (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    Over (fiberInclusion.obj (residueObj Λ k X hX)) ⥤ ArtinianLocalAlgCat Λ k :=
  sliceAt (forget Λ k) (residueObj Λ k X hX)

/-- `deformationForget` is the composite of the Over-forgetful functor with `forget`. -/
theorem deformationForget_eq (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    deformationForget Λ k X hX =
      Over.forget (fiberInclusion.obj (residueObj Λ k X hX)) ⋙ forget Λ k := sorry

/-- The unique retraction of the trivial dual-number pushforward, as a morphism of `Def_X`. -/
def trivialLiftHom (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    trivialObj Λ k X hX ⟶ fiberInclusion.obj (residueObj Λ k X hX) :=
  retraction (forget Λ k) (trivialPushforward Λ k X hX)

/-- The trivial dual-number lift of `X` in the slice `Def_X`. -/
def trivialLift (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    (deformationForget Λ k X hX).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k X hX).obj (Over.mk (trivialLiftHom Λ k X hX)) =
      dualNumber Λ k)

/-- The isomorphism-class functor of `Def_X` satisfies Schlessinger's (H2). -/
instance instHasSchlessingerH2_fiberIsoClass_deformationForget (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    HasSchlessingerH2 (fiberIsoClassFunctor (deformationForget Λ k X hX)) :=
  instHasSchlessingerH2_fiberIsoClass_sliceAt (forget Λ k) (residueObj Λ k X hX)

/-- The tangent space `T Def_X` is the type of isomorphism classes of the dual-number fibre. -/
abbrev tangentSpace (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :=
  (fiberIsoClassFunctor (deformationForget Λ k X hX)).obj (dualNumber Λ k)

/-- Unfolding of `tangentSpace`. -/
theorem tangentSpace_def (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    tangentSpace Λ k X hX =
      (fiberIsoClassFunctor (deformationForget Λ k X hX)).obj (dualNumber Λ k) := sorry

/-- Additive group structure on `T Def_X` from Lemma 90.12.2. -/
instance instAddCommGroup_tangentSpace (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    AddCommGroup (tangentSpace Λ k X hX) :=
  instAddCommGroup_fiberDualTangent (deformationForget Λ k X hX)

/-- `T Def_X` is a `k`-vector space, with scalars acting by dual-number pushforward. -/
instance instModule_tangentSpace (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    Module k (tangentSpace Λ k X hX) :=
  instModule_fiberDualTangent (deformationForget Λ k X hX)

/-- The isomorphism class of a dual-number lift of `X`. -/
def tangentSpaceMk (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX]
    (x : (deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    tangentSpace Λ k X hX :=
  Quotient.mk'' x

/-- `tangentSpaceMk` is the class of the given dual-number fibre object. -/
theorem tangentSpaceMk_eq (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX]
    (x : (deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    tangentSpaceMk Λ k X hX x = Quotient.mk'' x := sorry

/-- Two dual-number lifts determine the same tangent vector if and only if they are isomorphic. -/
theorem tangentSpaceMk_eq_mk (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX]
    (x y : (deformationForget Λ k X hX).Fiber (dualNumber Λ k)) :
    tangentSpaceMk Λ k X hX x = tangentSpaceMk Λ k X hX y ↔ Nonempty (x ≅ y) := sorry

/-- The zero tangent vector of `Def_X`. -/
def trivialTangent (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] : tangentSpace Λ k X hX :=
  tangentSpaceMk Λ k X hX (trivialLift Λ k X hX)

/-- `trivialTangent` is the class of the trivial dual-number lift. -/
theorem trivialTangent_eq (X : Scheme.{u})
    (hX : X ⟶ Spec (CommRingCat.of (residue Λ k).carrier))
    [AlgebraicGeometry.Flat hX] :
    trivialTangent Λ k X hX = tangentSpaceMk Λ k X hX (trivialLift Λ k X hX) := sorry

end FlatSchemeCat
