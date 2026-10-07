module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap90.Definition_90_19_2
public import stacks_project.Chap90.Lemma_90_16_6
public import stacks_project.Chap90.Lemma_90_19_9_Module
public import stacks_project.Chap90.Remark_90_12_5_TangentSpace
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass
public import stacks_project.Chap93.Example_93_11_1_Algebraic_spaces_Deformation
public import stacks_project.Chap93.Lemma_93_11_2_RimSchlessinger

/-!
# Trivial dual-number lift, Inf, and tangent space of `Def_X`

The trivial deformation `X' = X ×_{Spec k} Spec k[ε]` of an algebraic space over `k`,
together with `Inf(Def_X)` at this pushforward and `T Def_X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor Limits
open Functor.Fiber
open ArtinianLocalAlgCat
open scoped DualNumber

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatAlgebraicSpaceCat

/-- The structure morphism of `ofResidue X` is flat. -/
instance (priority := 1000) instFlat_ofResidue_structureHom
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    AlgebraicSpace.Flat (ofResidue Λ k X).structureHom :=
  (ofResidue Λ k X).isFlat

variable (X : AlgebraicSpace (Spec (CommRingCat.of k)))

/-- The trivial dual-number algebraic space `X ×_{Spec k} Spec k[ε]`. -/
def trivialSpace : AlgebraicSpace (specBase Λ) :=
  pullback (ofResidue Λ k X).structureHom (specMap (residueToDualNumber Λ k))

/-- `trivialSpace` is the pullback of the structure morphism along `Spec k[ε] ⟶ Spec k`. -/
theorem trivialSpace_eq :
    trivialSpace Λ k X =
      pullback (ofResidue Λ k X).structureHom (specMap (residueToDualNumber Λ k)) :=
  sorry

/-- The structure morphism of the trivial dual-number algebraic space over `Spec k[ε]`. -/
def trivialSpaceOver : trivialSpace Λ k X ⟶ specObj (dualNumber Λ k) :=
  pullback.snd (ofResidue Λ k X).structureHom (specMap (residueToDualNumber Λ k))

/-- The projection `X' ⟶ X` of the trivial dual-number thickening. -/
def trivialSpaceProj : trivialSpace Λ k X ⟶ (ofResidue Λ k X).space :=
  pullback.fst (ofResidue Λ k X).structureHom (specMap (residueToDualNumber Λ k))

/-- The closed immersion of `X` into the trivial dual-number thickening. -/
def trivialSpaceImmersion : (ofResidue Λ k X).space ⟶ trivialSpace Λ k X :=
  pullback.lift (𝟙 _)
    ((ofResidue Λ k X).structureHom ≫ specMap (dualNumberToResidue Λ k)) sorry

/-- `trivialSpaceImmersion` is the section of `trivialSpaceProj` induced by `k[ε] ⟶ k`. -/
theorem trivialSpaceImmersion_comp_proj :
    trivialSpaceImmersion Λ k X ≫ trivialSpaceProj Λ k X = 𝟙 _ :=
  sorry

/-- Base change of a flat morphism along `Spec k[ε] ⟶ Spec k` remains flat. -/
instance instFlat_trivialSpaceOver :
    AlgebraicSpace.Flat (trivialSpaceOver Λ k X) :=
  sorry

/-- The trivial dual-number object `(k[ε], X')` of `FlatAlgebraicSpaceCat`. -/
def trivialObj : FlatAlgebraicSpaceCat Λ k :=
  of (dualNumber Λ k) (trivialSpace Λ k X) (trivialSpaceOver Λ k X)
    (instFlat_trivialSpaceOver Λ k X)

/-- The base of `trivialObj` is `k[ε]`. -/
theorem trivialObj_base : (trivialObj Λ k X).base = dualNumber Λ k :=
  sorry

/-- The trivial dual-number deformation of `x0 = (k, X)` in the fibre of `forget`. -/
def trivialDeformation : (forget Λ k).Fiber (dualNumber Λ k) :=
  Fiber.mk (rfl : (forget Λ k).obj (trivialObj Λ k X) = dualNumber Λ k)

/-- The underlying object of `trivialDeformation` is `trivialObj`. -/
theorem trivialDeformation_obj :
    fiberInclusion.obj (trivialDeformation Λ k X) = trivialObj Λ k X :=
  sorry

/-- The canonical strongly cocartesian pushforward of `x0` along `k ⟶ k[ε]`. -/
def trivialPushforward :
    fiberInclusion.obj (residueObj Λ k X) ⟶
      fiberInclusion.obj (trivialDeformation Λ k X) :=
  Hom.of (residueToDualNumber Λ k) (trivialSpaceProj Λ k X)
    (IsPullback.of_hasPullback (ofResidue Λ k X).structureHom
      (specMap (residueToDualNumber Λ k)))

/-- The base map of `trivialPushforward` is `residueToDualNumber`. -/
theorem trivialPushforward_base :
    (forget Λ k).map (trivialPushforward Λ k X) = residueToDualNumber Λ k :=
  sorry

/-- The canonical pushforward of `x0` along `k ⟶ k[ε]` is strongly cocartesian. -/
instance instIsStronglyCocartesian_trivialPushforward :
    (forget Λ k).IsStronglyCocartesian (residueToDualNumber Λ k)
      (trivialPushforward Λ k X) :=
  sorry

/-- Infinitesimal automorphisms of `Def_X` at the trivial dual-number pushforward. -/
abbrev inf :=
  Functor.infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X)
    (trivialDeformation Λ k X) (trivialPushforward Λ k X)

/-- Unfolding of `inf`. -/
theorem inf_def :
    inf Λ k X =
      Functor.infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X)
        (trivialDeformation Λ k X) (trivialPushforward Λ k X) :=
  sorry

/-- Membership in `inf` is the equalizer condition along the unique retraction of the
chosen dual-number pushforward. -/
theorem mem_inf (α : Aut (trivialDeformation Λ k X)) :
    α ∈ Functor.infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X)
      (trivialDeformation Λ k X) (trivialPushforward Λ k X) ↔
      fiberInclusion.map α.hom ≫ retraction (forget Λ k) (trivialPushforward Λ k X) =
        retraction (forget Λ k) (trivialPushforward Λ k X) :=
  sorry

/-- Additive structure on `Inf(Def_X)` from Lemma 90.19.9. -/
instance instAddCommGroup_inf : AddCommGroup (inf Λ k X) :=
  instAddCommGroup_infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X)
    (trivialDeformation Λ k X) (trivialPushforward Λ k X)

/-- `k`-vector space structure on `Inf(Def_X)` from Lemma 90.19.9. -/
instance instModule_inf : Module k (inf Λ k X) :=
  instModule_infinitesimalAutomorphismsAt (forget Λ k) (residueObj Λ k X)
    (trivialDeformation Λ k X) (trivialPushforward Λ k X)

/-- The unique retraction of the trivial dual-number pushforward, as a morphism of `Def_X`. -/
def trivialLiftHom : trivialObj Λ k X ⟶ fiberInclusion.obj (residueObj Λ k X) :=
  retraction (forget Λ k) (trivialPushforward Λ k X)

/-- The trivial dual-number lift of `X` in the slice `Def_X`. -/
def trivialLift : (deformationForget Λ k X).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ k X).obj (Over.mk (trivialLiftHom Λ k X)) =
      dualNumber Λ k)

/-- The isomorphism-class functor of `Def_X` satisfies Schlessinger's (H2). -/
instance instHasSchlessingerH2_fiberIsoClass_deformationForget :
    HasSchlessingerH2 (fiberIsoClassFunctor (deformationForget Λ k X)) :=
  instHasSchlessingerH2_fiberIsoClass_sliceAt (forget Λ k) (residueObj Λ k X)

/-- The tangent space `T Def_X` is the type of isomorphism classes of the dual-number fibre. -/
abbrev tangentSpace :=
  (fiberIsoClassFunctor (deformationForget Λ k X)).obj (dualNumber Λ k)

/-- Unfolding of `tangentSpace`. -/
theorem tangentSpace_def :
    tangentSpace Λ k X =
      (fiberIsoClassFunctor (deformationForget Λ k X)).obj (dualNumber Λ k) :=
  sorry

/-- Additive group structure on `T Def_X` from Lemma 90.12.2. -/
instance instAddCommGroup_tangentSpace : AddCommGroup (tangentSpace Λ k X) :=
  instAddCommGroup_fiberDualTangent (deformationForget Λ k X)

/-- `T Def_X` is a `k`-vector space, with scalars acting by dual-number pushforward. -/
instance instModule_tangentSpace : Module k (tangentSpace Λ k X) :=
  instModule_fiberDualTangent (deformationForget Λ k X)

/-- The isomorphism class of a dual-number lift of `X`. -/
def tangentSpaceMk (x : (deformationForget Λ k X).Fiber (dualNumber Λ k)) :
    tangentSpace Λ k X :=
  Quotient.mk'' x

/-- `tangentSpaceMk` is the class of the given dual-number fibre object. -/
theorem tangentSpaceMk_eq (x : (deformationForget Λ k X).Fiber (dualNumber Λ k)) :
    tangentSpaceMk Λ k X x = Quotient.mk'' x :=
  sorry

/-- Two dual-number lifts determine the same tangent vector if and only if they are isomorphic. -/
theorem tangentSpaceMk_eq_mk (x y : (deformationForget Λ k X).Fiber (dualNumber Λ k)) :
    tangentSpaceMk Λ k X x = tangentSpaceMk Λ k X y ↔ Nonempty (x ≅ y) :=
  sorry

/-- The zero tangent vector of `Def_X`. -/
def trivialTangent : tangentSpace Λ k X :=
  tangentSpaceMk Λ k X (trivialLift Λ k X)

/-- `trivialTangent` is the class of the trivial dual-number lift. -/
theorem trivialTangent_eq :
    trivialTangent Λ k X = tangentSpaceMk Λ k X (trivialLift Λ k X) :=
  sorry

end FlatAlgebraicSpaceCat
