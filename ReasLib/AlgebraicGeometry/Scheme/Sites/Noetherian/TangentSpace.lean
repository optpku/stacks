/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.TangentSpace
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.DualNumber
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Types
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Scheme
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.DualNumber
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.RimSchlessinger

/-!
# Tangent spaces of Type-valued functors on locally Noetherian schemes

A Type-valued functor on locally Noetherian schemes over `S` restricts along
`specOver` to a functor on `ArtinianLocalAlgCat`. Pointing at a finite-type
field point `x0` produces a predeformation functor whose tangent space is
`TF_{k, x0}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TypeCat
open AlgebraicGeometry.GroupoidsOver.Predeformation
open ArtinianLocalAlgCat
open CategoryTheory.Functor

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Over

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- Spectra of Artinian local algebras, viewed over `S` through the chosen affine
open, are locally Noetherian. -/
instance instIsLocallyNoetherian_specOver
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (A : ArtinianLocalAlgCat Λ k) :
    IsLocallyNoetherian (specOver openImmersion A).left := by
  change IsLocallyNoetherian (Spec (CommRingCat.of A.carrier))
  infer_instance

/-- The spectrum of a finite-type field over `S` is locally Noetherian. -/
instance instIsLocallyNoetherian_specField
    (f : Spec (CommRingCat.of k) ⟶ S) :
    IsLocallyNoetherian (Over.mk f).left := by
  change IsLocallyNoetherian (Spec (CommRingCat.of k))
  infer_instance

/-- Restriction of a Type-valued functor on locally Noetherian schemes over `S`
along `specOver`. -/
def artinianEval (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion] :
    ArtinianLocalAlgCat Λ k ⥤ Type v where
  obj A := F.obj (op (asLocallyNoetherian (specOver openImmersion A)))
  map f := F.map (op (asLocallyNoetherianMap (specOverMap openImmersion f)))
  map_id A := by
    have h : (asLocallyNoetherianMap (specOverMap openImmersion (𝟙 A))).op =
        𝟙 (op (asLocallyNoetherian (specOver openImmersion A))) := by
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      exact congrArg Quiver.Hom.unop ((specFunctor openImmersion).map_id A)
    exact (congrArg F.map h).trans (F.map_id _)
  map_comp f g := by
    have h : (asLocallyNoetherianMap (specOverMap openImmersion (f ≫ g))).op =
        (asLocallyNoetherianMap (specOverMap openImmersion f)).op ≫
          (asLocallyNoetherianMap (specOverMap openImmersion g)).op := by
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      exact congrArg Quiver.Hom.unop ((specFunctor openImmersion).map_comp f g)
    exact (congrArg F.map h).trans (F.map_comp _ _)

/-- The object map of `artinianEval` is evaluation of `F` on `specOver A`. -/
theorem artinianEval_obj (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (A : ArtinianLocalAlgCat Λ k) :
    (artinianEval F openImmersion).obj A =
      F.obj (op (asLocallyNoetherian (specOver openImmersion A))) :=
  sorry

/-- The morphism map of `artinianEval` is restriction of `F` along `specOverMap`. -/
theorem artinianEval_map (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B)
    (x : (artinianEval F openImmersion).obj A) :
    (artinianEval F openImmersion).map f x =
      F.map (op (asLocallyNoetherianMap (specOverMap openImmersion f))) x :=
  sorry

variable (F : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type v)
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (x0 : F.obj (op (asLocallyNoetherian (Over.mk kToS))))

/-- `specOver` of the residue field is the finite-type point `Over.mk kToS`. -/
theorem specOver_residue :
    specOver openImmersion (ArtinianLocalAlgCat.residue Λ k) = Over.mk kToS :=
  sorry

/-- Transport of `x0 ∈ F(Spec(k))` to the value of `artinianEval` at the residue
object. -/
def residueSection : (artinianEval F openImmersion).obj (ArtinianLocalAlgCat.residue Λ k) :=
  eqToHom
    (congrArg (fun f : Spec (CommRingCat.of k) ⟶ S =>
        F.obj (op (asLocallyNoetherian (Over.mk f))))
      h_factor.symm)
    x0

/-- `residueSection x0` is the transport of `x0` along `specOver_residue`. -/
theorem residueSection_eq :
    residueSection F openImmersion kToS h_factor x0 =
      eqToHom
        (congrArg (fun f : Spec (CommRingCat.of k) ⟶ S =>
            F.obj (op (asLocallyNoetherian (Over.mk f))))
          h_factor.symm)
        x0 :=
  sorry

/-- Restriction of a value of `artinianEval` along `Spec(k) ⟶ Spec(A)`. -/
def restrictionToResidue (A : ArtinianLocalAlgCat Λ k)
    (x : (artinianEval F openImmersion).obj A) :
    F.obj (op (asLocallyNoetherian (Over.mk kToS))) :=
  F.map (op (asLocallyNoetherianMap (specOver_toResidue openImmersion kToS h_factor A))) x

/-- Restriction to the residue point commutes with a morphism of Artinian local algebras. -/
theorem restrictionToResidue_naturality {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B)
    (x : (artinianEval F openImmersion).obj A) :
    restrictionToResidue F openImmersion kToS h_factor B
        ((artinianEval F openImmersion).map f x) =
      restrictionToResidue F openImmersion kToS h_factor A x := sorry

/-- The pointed restriction `F_{k, x0}` of `F` to Artinian local algebras. -/
def evalAt : ArtinianLocalAlgCat Λ k ⥤ Type v where
  obj A := { x : (artinianEval F openImmersion).obj A //
    restrictionToResidue F openImmersion kToS h_factor A x = x0 }
  map f := ofHom fun x ↦
    ⟨(artinianEval F openImmersion).map f x.val,
      (restrictionToResidue_naturality F openImmersion kToS h_factor f x.val).trans x.property⟩
  map_id A := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (artinianEval F openImmersion).map_id_apply A x.val
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact (artinianEval F openImmersion).map_comp_apply f g x.val

/-- The underlying value of a pointed evaluation on `Spec(A)`. -/
def evalAt.val {A : ArtinianLocalAlgCat Λ k}
    (x : (evalAt F openImmersion kToS h_factor x0).obj A) :
    (artinianEval F openImmersion).obj A :=
  x.val

/-- A value of `artinianEval` restricting to `x0` determines a point of `evalAt`. -/
def evalAt.mk {A : ArtinianLocalAlgCat Λ k}
    (x : (artinianEval F openImmersion).obj A)
    (hx : restrictionToResidue F openImmersion kToS h_factor A x = x0) :
    (evalAt F openImmersion kToS h_factor x0).obj A :=
  ⟨x, hx⟩

/-- Points of `evalAt` are values of `artinianEval` whose restriction along
`specOver_toResidue` is `x0`. -/
theorem evalAt_obj {A : ArtinianLocalAlgCat Λ k}
    (x : (evalAt F openImmersion kToS h_factor x0).obj A) :
    restrictionToResidue F openImmersion kToS h_factor A
        (evalAt.val F openImmersion kToS h_factor x0 x) = x0 :=
  sorry

/-- `evalAt` is a predeformation functor: its value at the residue field is a
singleton. -/
instance instIsPredeformationFunctor_evalAt :
    IsPredeformationFunctor (evalAt F openImmersion kToS h_factor x0) :=
  sorry

/-- If `F` satisfies (RS), then `evalAt` satisfies Schlessinger's (H2). -/
instance instHasSchlessingerH2_evalAt [HasRimSchlessinger F] :
    HasSchlessingerH2 (evalAt F openImmersion kToS h_factor x0) :=
  sorry

/-- The tangent space `TF_{k, x0}` of a Type-valued functor on locally Noetherian
schemes over `S`. -/
abbrev tangentSpace : Type v :=
  IsPredeformationFunctor.tangentSpace (evalAt F openImmersion kToS h_factor x0)

/-- `TF_{k, x0}` is the value of `evalAt` at the dual-number object. -/
theorem tangentSpace_eq :
    tangentSpace F openImmersion kToS h_factor x0 =
      (evalAt F openImmersion kToS h_factor x0).obj (ArtinianLocalAlgCat.dualNumber Λ k) :=
  sorry

/-- A value of `F` on `Spec(k[ε])` restricting to `x0` along
`Spec(k) ⟶ Spec(k[ε])` is a tangent vector. -/
def tangentSpace.mk
    (x : (artinianEval F openImmersion).obj (ArtinianLocalAlgCat.dualNumber Λ k))
    (hx : restrictionToResidue F openImmersion kToS h_factor
        (ArtinianLocalAlgCat.dualNumber Λ k) x = x0) :
    tangentSpace F openImmersion kToS h_factor x0 :=
  evalAt.mk F openImmersion kToS h_factor x0 x hx

/-- The underlying dual-number value of a tangent vector. -/
def tangentSpace.val (x : tangentSpace F openImmersion kToS h_factor x0) :
    (artinianEval F openImmersion).obj (ArtinianLocalAlgCat.dualNumber Λ k) :=
  evalAt.val F openImmersion kToS h_factor x0 x

/-- Restriction of a tangent vector along `specOver_toResidue` of `dualNumber`
recovers `x0`. -/
theorem tangentSpace.restriction_eq
    (x : tangentSpace F openImmersion kToS h_factor x0) :
    restrictionToResidue F openImmersion kToS h_factor (ArtinianLocalAlgCat.dualNumber Λ k)
        (tangentSpace.val F openImmersion kToS h_factor x0 x) = x0 :=
  sorry

end AlgebraicGeometry.Scheme.Over
