/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Finite.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Orbits

/-!
# Orbit quotient of restricted coyoneda of dual numbers

The set-valued functor `underline{k[ε]}/G` is the pointwise orbit quotient of
`restrictedCoyoneda (toComplete (dualNumber Λ k))` by a subgroup
`G ≤ Aut (dualNumber Λ k)`. The associated predeformation category is the
Hom-universe lift of its category of elements, matching `identityProjection`.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt
open scoped BasedFunctor

universe u v w

noncomputable section

namespace ArtinianLocalAlgCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The dual numbers `k[ε]` as an object of `CompleteLocalAlgCat Λ k`. -/
abbrev dualNumberComplete : CompleteLocalAlgCat Λ k :=
  toComplete (dualNumber Λ k)

/-- `dualNumberComplete` is `toComplete` of the bundled dual-number object. -/
theorem dualNumberComplete_eq :
    dualNumberComplete Λ k = toComplete (dualNumber Λ k) := rfl

/-- Restricted coyoneda of `k[ε]`, i.e. the functor `underline{k[ε]}` on `C_Λ`. -/
abbrev restrictedDualNumber : ArtinianLocalAlgCat Λ k ⥤ Type u :=
  CompleteLocalAlgCat.restrictedCoyoneda (dualNumberComplete Λ k)

/-- On objects, `restrictedDualNumber` is `Hom` out of `dualNumberComplete`. -/
theorem restrictedDualNumber_obj (A : ArtinianLocalAlgCat Λ k) :
    (restrictedDualNumber Λ k).obj A =
      (dualNumberComplete Λ k ⟶ inclusion.obj A) := rfl

variable {Λ k}

/-- Precomposition action of `Aut (dualNumber Λ k)` on `underline{k[ε]}(A)`. -/
def smul (g : Aut (dualNumber Λ k)) {A : ArtinianLocalAlgCat Λ k}
    (x : (restrictedDualNumber Λ k).obj A) : (restrictedDualNumber Λ k).obj A :=
  inclusion.map g.symm.hom ≫ x

/-- The automorphism `g` acts by precomposition with `inclusion.map g.symm.hom`. -/
theorem smul_def (g : Aut (dualNumber Λ k)) {A : ArtinianLocalAlgCat Λ k}
    (x : (restrictedDualNumber Λ k).obj A) :
    smul g x = inclusion.map g.symm.hom ≫ x := rfl

/-- The identity automorphism acts as the identity. -/
theorem smul_one {A : ArtinianLocalAlgCat Λ k} (x : (restrictedDualNumber Λ k).obj A) :
    smul (1 : Aut (dualNumber Λ k)) x = x := sorry

/-- The action of a product of automorphisms is the composite action. -/
theorem smul_mul (g h : Aut (dualNumber Λ k)) {A : ArtinianLocalAlgCat Λ k}
    (x : (restrictedDualNumber Λ k).obj A) :
    smul (g * h) x = smul g (smul h x) := sorry

/-- Automorphisms of `k[ε]` act on `underline{k[ε]}(A)` by precomposition. -/
instance instMulAction_aut_restrictedDualNumber {A : ArtinianLocalAlgCat Λ k} :
    MulAction (Aut (dualNumber Λ k)) ((restrictedDualNumber Λ k).obj A) where
  smul g x := smul g x
  one_smul := smul_one
  mul_smul left right point := smul_mul left right point

variable (G : Subgroup (Aut (dualNumber Λ k)))

/-- The scalar by which an automorphism of the dual numbers acts on the square-zero
ideal, computed by applying it to ε and taking its infinitesimal coefficient. -/
def epsilonScale (g : Aut (dualNumber Λ k)) : k :=
  (g.hom.hom (TrivSqZeroExt.inr (1 : k))).snd

/-- A derivation of the dual numbers gives the residue-compatible dual-number point
whose scalar coordinate is the residue and whose infinitesimal coordinate is the derivation. -/
def dualNumberPointOfDerivation
    (D : Derivation Λ (dualNumberComplete Λ k).carrier k) :
    (restrictedDualNumber Λ k).obj (dualNumber Λ k) :=
  let point : CompleteLocalAlgCat.algebraHom (dualNumberComplete Λ k)
      (inclusion.obj (dualNumber Λ k)) := FormalObject.toDualNumber D
  let laws : IsLocalHom point ∧
      ∀ localHom : IsLocalHom point,
        CompleteLocalAlgCat.residueCompat point localHom =
          CompleteLocalAlgCat.residueIsoHom (dualNumberComplete Λ k) := sorry
  CompleteLocalAlgCat.Hom.of point laws.1 (laws.2 laws.1)

/-- The orbit relation of `G` on `underline{k[ε]}(A)`. -/
def orbitRel (A : ArtinianLocalAlgCat Λ k) (x y : (restrictedDualNumber Λ k).obj A) :
    Prop :=
  ∃ g : G, g • x = y

/-- Two maps out of `k[ε]` lie in the same `G`-orbit iff some element of `G` carries
one to the other. -/
theorem orbitRel_iff {A : ArtinianLocalAlgCat Λ k}
    (x y : (restrictedDualNumber Λ k).obj A) :
    orbitRel G A x y ↔ ∃ g : G, g • x = y := Iff.rfl

/-- Postcomposition with a morphism of `C_Λ` preserves `G`-orbits. -/
theorem orbitRel_map {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B)
    {x y : (restrictedDualNumber Λ k).obj A} (h : orbitRel G A x y) :
    orbitRel G B ((restrictedDualNumber Λ k).map f x)
      ((restrictedDualNumber Λ k).map f y) := sorry

/-- The orbit-quotient functor `underline{k[ε]}/G`. -/
def quotientBy : ArtinianLocalAlgCat Λ k ⥤ Type u :=
  let quotientMap : ∀ {A B : ArtinianLocalAlgCat Λ k},
      (A ⟶ B) → (Quot (orbitRel G A) ⟶ Quot (orbitRel G B)) :=
    fun f ↦ TypeCat.ofHom
      (Quot.map ((restrictedDualNumber Λ k).map f) fun _ _ related ↦
        orbitRel_map G f related)
  let laws : (∀ A, quotientMap (𝟙 A) = 𝟙 (Quot (orbitRel G A))) ∧
      (∀ {A B C : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) (g : B ⟶ C),
        quotientMap (f ≫ g) = quotientMap f ≫ quotientMap g) := sorry
  { obj A := Quot (orbitRel G A)
    map := quotientMap
    map_id := laws.1
    map_comp := laws.2 }

/-- The value of `quotientBy G` at `A` is the quotient of `underline{k[ε]}(A)` by `G`. -/
theorem quotientBy_obj (A : ArtinianLocalAlgCat Λ k) :
    (quotientBy G).obj A = Quot (orbitRel G A) := rfl

/-- Restriction in `quotientBy G` is induced by restriction of representatives. -/
theorem quotientBy_map_mk {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B)
    (x : (restrictedDualNumber Λ k).obj A) :
    (quotientBy G).map f (Quot.mk (orbitRel G A) x) =
      Quot.mk (orbitRel G B) ((restrictedDualNumber Λ k).map f x) := rfl

/-- The quotient map `underline{k[ε]} ⟶ underline{k[ε]}/G`. -/
def quotientMk : restrictedDualNumber Λ k ⟶ quotientBy G where
  app A := TypeCat.ofHom (Quot.mk (orbitRel G A))
  naturality := sorry

/-- The component of `quotientMk` at `A` is `Quot.mk`. -/
theorem quotientMk_app (A : ArtinianLocalAlgCat Λ k)
    (x : (restrictedDualNumber Λ k).obj A) :
    (quotientMk G).app A x = Quot.mk (orbitRel G A) x := rfl

/-- Hom-universe lift of the category of elements of `underline{k[ε]}/G`, matching
the universe constraint of `FormalObject`. -/
abbrev quotientTotal : Type (u + 1) :=
  ULiftHom.{u + 1} (quotientBy G).Elements

/-- `quotientTotal G` is the Hom-universe lift of the category of elements of
`quotientBy G`. -/
theorem quotientTotal_eq :
    quotientTotal G = ULiftHom.{u + 1} (quotientBy G).Elements := rfl

/-- Projection of the Hom-universe lift of `underline{k[ε]}/G` to `C_Λ`. -/
def quotientProjection : quotientTotal G ⥤ ArtinianLocalAlgCat Λ k :=
  (ULiftHom.down : quotientTotal G ⥤ (quotientBy G).Elements) ⋙
    CategoryOfElements.π (quotientBy G)

/-- `quotientProjection` is the category-of-elements projection after Hom-universe
forgetful. -/
theorem quotientProjection_eq :
    quotientProjection G =
      (ULiftHom.down : quotientTotal G ⥤ (quotientBy G).Elements) ⋙
        CategoryOfElements.π (quotientBy G) := rfl

/-- The based functor `underline{k[ε]} ⟶ underline{k[ε]}/G` induced by `quotientMk`. -/
def quotientBasedFunctor :
    BasedCategory.ofFunctor
        (CompleteLocalAlgCat.identityProjection (dualNumberComplete Λ k)) ⥤ᵇ
      BasedCategory.ofFunctor (quotientProjection G) :=
  BasedFunctor.ofFunctor
    ((ULiftHom.down :
        CompleteLocalAlgCat.identityTotal (dualNumberComplete Λ k) ⥤
          (restrictedDualNumber Λ k).Elements) ⋙
      CategoryOfElements.map (quotientMk G) ⋙
      (ULiftHom.up : (quotientBy G).Elements ⥤ quotientTotal G))
    sorry

/-- The underlying total functor of `quotientBasedFunctor` is the Hom-universe lift
of `CategoryOfElements.map (quotientMk G)`. -/
theorem quotientBasedFunctor_eq :
    (quotientBasedFunctor G).toFunctor =
      (ULiftHom.down :
          CompleteLocalAlgCat.identityTotal (dualNumberComplete Λ k) ⥤
            (restrictedDualNumber Λ k).Elements) ⋙
        CategoryOfElements.map (quotientMk G) ⋙
        (ULiftHom.up : (quotientBy G).Elements ⥤ quotientTotal G) := rfl

/-- Stage `n` of `quotientFormalObject`, the image of the identity truncation of
`k[ε]` under `quotientBasedFunctor`. -/
def quotientStage (n : ℕ) : quotientTotal G :=
  (quotientBasedFunctor G).obj
    (CompleteLocalAlgCat.identityStage (dualNumberComplete Λ k) n)

/-- `quotientStage G n` is the image of `identityStage` under `quotientBasedFunctor`. -/
theorem quotientStage_eq (n : ℕ) :
    quotientStage G n =
      (quotientBasedFunctor G).obj
        (CompleteLocalAlgCat.identityStage (dualNumberComplete Λ k) n) := rfl

/-- Successor transition of `quotientStage`. -/
def quotientStageMap (n : ℕ) : quotientStage G (n + 1) ⟶ quotientStage G n :=
  (quotientBasedFunctor G).map
    (CompleteLocalAlgCat.identityStageMap (dualNumberComplete Λ k) n)

/-- `quotientStageMap` is the image of `identityStageMap` under `quotientBasedFunctor`. -/
theorem quotientStageMap_eq (n : ℕ) :
    quotientStageMap G n =
      (quotientBasedFunctor G).map
        (CompleteLocalAlgCat.identityStageMap (dualNumberComplete Λ k) n) := rfl

/-- The formal object of `underline{k[ε]}/G` obtained by pushing identity truncations
of `k[ε]` along `quotientBasedFunctor`. -/
def quotientFormalObject : FormalObject (quotientProjection G) :=
  let laws : (∀ n, (quotientProjection G).obj (quotientStage G n) =
        (dualNumberComplete Λ k).truncation n) ∧
      (∀ n, (quotientProjection G).IsHomLift
        ((dualNumberComplete Λ k).truncationMap n) (quotientStageMap G n)) := sorry
  FormalObject.of (dualNumberComplete Λ k) (quotientStage G) (quotientStageMap G)
    laws.1 laws.2

/-- The complete local base of `quotientFormalObject G` is `dualNumberComplete`. -/
theorem quotientFormalObject_base :
    (quotientFormalObject G).base = dualNumberComplete Λ k := rfl

/-- `quotientBasedFunctor G` represents `quotientFormalObject G`. -/
theorem quotientFormalObject_represents :
    FormalObject.Represents (quotientFormalObject G) (quotientBasedFunctor G) := sorry

/-- The Hom-universe lift of the category of elements of `underline{k[ε]}/G` is
cofibered in groupoids over `C_Λ`. -/
instance instIsFiberedInGroupoids_quotientProjection_op :
    Functor.IsFibered.InGroupoids (quotientProjection G).op := sorry

/-- The dual-number fibre object of `quotientProjection G` with component `q`. -/
def orbitQuotientElement (q : Quot (orbitRel G (dualNumber Λ k))) : quotientTotal G :=
  ULiftHom.objUp ⟨dualNumber Λ k, q⟩

/-- `orbitQuotientElement G q` lies over `dualNumber`. -/
theorem orbitQuotientElement_obj (q : Quot (orbitRel G (dualNumber Λ k))) :
    (quotientProjection G).obj (orbitQuotientElement G q) = dualNumber Λ k := rfl

/-- The orbit quotient of the dual-number represented functor is a predeformation category. -/
instance instIsPredeformationCategory_quotientProjection :
    Functor.IsPredeformationCategory (quotientProjection G) := sorry

/-- The image of the identity dual-number tower is a versal formal object of its orbit quotient. -/
instance instIsVersal_quotientFormalObject :
    FormalObject.IsVersal (quotientFormalObject G) := sorry

/-- The quotient formal object has bijective differential on residue-derivation orbits exactly when every subgroup element has infinitesimal scaling coefficient one. -/
theorem bijectiveDifferentialOnOrbits_quotientFormalObject :
    FormalObject.BijectiveDifferentialOnOrbits (quotientFormalObject G) ↔
      ∀ g : G, epsilonScale g.val = 1 := sorry

/-- The quotient by a finite nontrivial dual-number automorphism subgroup fails Schlessinger's condition (S2). -/
theorem not_hasSchlessingerS2_quotientProjection [Finite G] (h_nontrivial : G ≠ ⊥) :
    ¬ Functor.HasSchlessingerS2 (quotientProjection G) := sorry

/-- The based quotient map of the dual-number represented functor is smooth. -/
instance instIsSmooth_quotientBasedFunctor :
    BasedFunctor.IsSmooth (quotientBasedFunctor G) := sorry

/-- The comparison from automorphism orbits of dual-number points to the tangent
space of the orbit quotient. -/
noncomputable def tangentSpaceMkQuot (q : Quot (orbitRel G (dualNumber Λ k))) :
    Functor.tangentSpace (quotientProjection G) :=
  Functor.tangentSpace.mk (quotientProjection G)
    (Functor.Fiber.mk
      (rfl : (quotientProjection G).obj (orbitQuotientElement G q) = dualNumber Λ k))

/-- The comparison `tangentSpaceMkQuot` evaluates as the isomorphism class of the
dual-number fibre object with component `q`. -/
theorem tangentSpaceMkQuot_eq (q : Quot (orbitRel G (dualNumber Λ k))) :
    tangentSpaceMkQuot G q =
      Functor.tangentSpace.mk (quotientProjection G)
        (Functor.Fiber.mk
          (rfl : (quotientProjection G).obj (orbitQuotientElement G q) =
            dualNumber Λ k)) := rfl

/-- The differential of the pushed identity formal object is the tangent class of
the actual dual-number point associated to the derivation, followed by the quotient. -/
theorem differential_quotientFormalObject
    (D : Derivation Λ (dualNumberComplete Λ k).carrier k) :
    FormalObject.differential (quotientFormalObject G) D =
      tangentSpaceMkQuot G
        (Quot.mk (orbitRel G (dualNumber Λ k)) (dualNumberPointOfDerivation D)) := sorry

/-- Two tangent images of the quotient formal object have the same residue-derivation
orbit exactly when their infinitesimal coefficients differ by a scaling from `G`. -/
theorem differential_orbit_iff_epsilonScale
    (D₁ D₂ : Derivation Λ (dualNumberComplete Λ k).carrier k) :
    FormalObject.differential (quotientFormalObject G) D₁ ∈
        AddAction.orbit (Derivation Λ k k)
          (FormalObject.differential (quotientFormalObject G) D₂) ↔
      ∃ g : G, D₁ (TrivSqZeroExt.inr (1 : k)) =
        epsilonScale g.val * D₂ (TrivSqZeroExt.inr (1 : k)) := sorry

/-- For a finite automorphism subgroup, the orbit classes of dual-number points map bijectively to the tangent space of the quotient. -/
theorem tangentSpace_quotientBy [Finite G] :
    Function.Bijective (tangentSpaceMkQuot G) := sorry


end ArtinianLocalAlgCat

end
