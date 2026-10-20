/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Stalk
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable {X : Scheme.{u}}

/- Remark 59.77.4 (1): Every geometric stalk term of a bounded constructible flat étale module
sheaf complex over a Noetherian ring is finite projective. -/
@[stacks 03TR] #check (AlgebraicGeometry.Scheme.Etale.finiteProjective_stalkTerm :
  ∀ (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ)
    (hbounded : ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b)
    (hconstructible : ∀ p, Scheme.Etale.IsConstructibleModule (K.X p))
    (hflat : ∀ p, Scheme.Etale.IsStalkwiseFlatModule (K.X p))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (geometricPoint : Spec (.of Ω) ⟶ X) (p : ℤ),
    Module.FiniteProjective Λ ((Scheme.Etale.moduleStalkComplex geometricPoint K).X p))

/- Remark 59.77.4 (2): Every geometric stalk complex of a bounded constructible flat étale
module sheaf complex over a Noetherian ring represents a perfect complex. -/
@[stacks 03TR] #check (AlgebraicGeometry.Scheme.Etale.isPerfect_stalkComplex :
  ∀ (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ)
    (hbounded : ∃ a b : ℤ, K.IsStrictlyGE a ∧ K.IsStrictlyLE b)
    (hconstructible : ∀ p, Scheme.Etale.IsConstructibleModule (K.X p))
    (hflat : ∀ p, Scheme.Etale.IsStalkwiseFlatModule (K.X p))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (geometricPoint : Spec (.of Ω) ⟶ X),
    DerivedCategory.IsPerfect
      (DerivedCategory.Q.obj (Scheme.Etale.moduleStalkComplex geometricPoint K)))
