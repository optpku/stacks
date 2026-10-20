/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GabberBound

/-!
# Example 85.23.2

Unbounded cohomological descent data on the locally finite type étale site of an allowed base,
with constant finite coefficients.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/- Example 85.23.2: cohomology vanishes above the Gabber bound for selected coverings. -/
@[stacks 0DC6] #check (AlgebraicGeometry.Scheme.Etale.higherCohomology_isZero : ∀ {S : Scheme.{u}} {Λ : Type u} [Ring Λ]
    [Finite Λ] [HasWeakSheafify (etaleTopology S) RingCat.{u}]
    (hS : IsFiniteEtaleCoefficientBase S) (hΛ : orderInvertible S Λ)
    {V : locallyOfFiniteTypeOver S} (hV : quasiCompact S V)
    [HasSheafify ((etaleTopology S).over V) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf ((etaleTopology S).over V) AddCommGrpCat.{u})]
    {cover : FormalCoproduct.{u} (Over V)} (hcover : cover ∈ coveringSystem S V)
    (i : cover.I) (p : ℕ) (hp : cohomologyBound V < p)
    (ℱ : SheafOfModules.{u} ((constantRingSheaf S Λ).over V)),
    IsZero
      (Sheaf.cohomologyOverObject
        ((SheafOfModules.toSheaf ((constantRingSheaf S Λ).over V)).obj ℱ)
        (cover.obj i) p))

/- Restriction of module sheaves along a morphism in the slice. -/
#check (AlgebraicGeometry.Scheme.Etale.restriction : ∀ {S : Scheme.{u}} {Λ : Type u} [Ring Λ]
    [HasWeakSheafify (etaleTopology S) RingCat.{u}]
    {U V : locallyOfFiniteTypeOver S} (f : U ⟶ V)
    (ℱ : SheafOfModules.{u} ((constantRingSheaf S Λ).over V)),
    (⊤ : ObjectProperty (SheafOfModules.{u} ((constantRingSheaf S Λ).over U)))
      ((SheafOfModules.overMap (constantRingSheaf S Λ) f).obj ℱ))

/- Membership in the module category is local for étale coverings. -/
#check (AlgebraicGeometry.Scheme.Etale.local_iff : ∀ {S : Scheme.{u}} {Λ : Type u} [Ring Λ]
    [HasWeakSheafify (etaleTopology S) RingCat.{u}]
    {U : locallyOfFiniteTypeOver S} {cover : FormalCoproduct.{u} (Over U)}
    (hcover : ((etaleTopology S).over U).CoversTop cover.obj)
    (ℱ : SheafOfModules.{u} ((constantRingSheaf S Λ).over U)),
    (⊤ : ObjectProperty (SheafOfModules.{u} ((constantRingSheaf S Λ).over U))) ℱ ↔
      ∀ i : cover.I,
        (⊤ : ObjectProperty
            (SheafOfModules.{u} ((constantRingSheaf S Λ).over (cover.obj i).left)))
          ((SheafOfModules.overMap (constantRingSheaf S Λ) (cover.obj i).hom).obj ℱ))

end AlgebraicGeometry.Scheme.Etale
