/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImageStalk
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite.Stalk
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.RingTheory.Finiteness.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable {X : Scheme.{u}}

/-- An étale module sheaf is constructible if every affine open has a finite constructible
locally closed stratification on which its canonical pullbacks are locally constant of finite
type. -/
def IsConstructibleModule (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) : Prop :=
  Sheaf.IsConstructibleEtaleModule
    (fun {Y} f ↦
      ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        X.smallEtaleTopology Y.smallEtaleTopology).obj)
    (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ↦
      Sheaf.IsFiniteTypeLocallyConstantModule G) F

set_option backward.isDefEq.respectTransparency false in
/-- A constructible module sheaf has finite-type geometric stalks. Choose a
stratum containing the point and transport its finite local constant model
through the inverse-image comparison. -/
theorem finite_stalk_of_isConstructibleModule
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : IsConstructibleModule F)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Module.Finite Λ (((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u} Λ)).obj F) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (s default)) isOpen_univ
  change X.Opens at U
  have hsU : Set.range s ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z default] using hxU
  let sU := IsOpenImmersion.lift U.ι s hsU
  have hsUfac : sU ≫ U.ι = s := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨Q, hQ, hstrata⟩ := hF U hU
  obtain ⟨T, ⟨hT, hxT⟩, -⟩ := Q.isPartition.2 (sU default)
  let T' : TopologicalSpace.LocallyCloseds U.toScheme :=
    ⟨T, Q.locallyClosed_of_mem hT⟩
  have hst : Set.range sU ⊆ T' := by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z default] using hxT
  let t := Scheme.LocallyClosedReduction.lift T' sU hst
  let j := Scheme.LocallyClosedReduction.ι T' ≫ U.ι
  have ht : t ≫ j = s := by
    dsimp [t, j]
    rw [← Category.assoc, Scheme.LocallyClosedReduction.lift_ι, hsUfac]
  let xbar := Scheme.GeometricPoint.of Ω t
  let G := ((Scheme.smallEtalePullback j).sheafPullback (ModuleCat.{u} Λ)
    X.smallEtaleTopology (Scheme.LocallyClosedReduction.scheme T').smallEtaleTopology).obj F
  have hG : Sheaf.IsFiniteTypeLocallyConstantModule G := (hstrata ⟨T, hT⟩).2
  letI : Module.Finite Λ (((Scheme.GeometricPoint.toSmallEtalePoint xbar).sheafFiber (A := ModuleCat.{u} Λ)).obj G) :=
    Sheaf.IsFiniteTypeLocallyConstantModule.finite_sheafFiber hG _
  let e := Scheme.smallEtaleInverseImage_stalkIsoWithCoefficients j xbar (ModuleCat.{u} Λ) F
  have hf := Module.Finite.equiv e.toLinearEquiv
  change Module.Finite Λ
    (((Scheme.pointSmallEtale (t ≫ j)).sheafFiber (A := ModuleCat.{u} Λ)).obj F) at hf
  rwa [ht] at hf

/-- Every term of a geometric stalk of a bounded complex of constructible stalkwise flat étale
module sheaves over a Noetherian ring is finite projective. -/
theorem finiteProjective_stalkTerm
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ)
    (hbounded : ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b)
    (hconstructible : ∀ p, IsConstructibleModule (K.X p))
    (hflat : ∀ p, IsStalkwiseFlatModule (K.X p))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (geometricPoint : Spec (.of Ω) ⟶ X)
    (p : ℤ) :
    Module.FiniteProjective Λ ((moduleStalkComplex geometricPoint K).X p) := by
  change Module.FiniteProjective Λ
    (((Scheme.pointSmallEtale geometricPoint).sheafFiber (A := ModuleCat.{u} Λ)).obj (K.X p))
  letI := finite_stalk_of_isConstructibleModule (K.X p) (hconstructible p) geometricPoint
  letI := hflat p Ω geometricPoint
  letI := Module.finitePresentation_of_finite Λ
    (((Scheme.pointSmallEtale geometricPoint).sheafFiber (A := ModuleCat.{u} Λ)).obj (K.X p))
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

/-- A geometric stalk of a bounded complex of constructible stalkwise flat étale module sheaves
over a Noetherian ring represents a perfect derived object. -/
theorem isPerfect_stalkComplex
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ)
    (hbounded : ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b)
    (hconstructible : ∀ p, IsConstructibleModule (K.X p))
    (hflat : ∀ p, IsStalkwiseFlatModule (K.X p))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (geometricPoint : Spec (.of Ω) ⟶ X) :
    DerivedCategory.IsPerfect
      (DerivedCategory.Q.obj (moduleStalkComplex geometricPoint K)) := sorry

end AlgebraicGeometry.Scheme.Etale
