/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Stalk
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

/-- Every term of a geometric stalk of a bounded complex of constructible stalkwise flat étale
module sheaves over a Noetherian ring is finite projective. -/
theorem finiteProjective_stalkTerm
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ)
    (hbounded : ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b)
    (hconstructible : ∀ p, IsConstructibleModule (K.X p))
    (hflat : ∀ p, IsStalkwiseFlatModule (K.X p))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (geometricPoint : Spec (.of Ω) ⟶ X)
    (p : ℤ) :
    Module.FiniteProjective Λ ((moduleStalkComplex geometricPoint K).X p) := sorry

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
