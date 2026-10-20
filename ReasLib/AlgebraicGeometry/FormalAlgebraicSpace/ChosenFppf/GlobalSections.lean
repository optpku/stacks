/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Topology.Defs.Induced
public import Mathlib.CategoryTheory.Category.Preorder
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation

/-!
# Global sections of directed affine diagrams
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- The inverse limit of global sections of an affine diagram consists of
families compatible with the restriction maps on global sections. -/
def limitGlobalSections {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S) :
    Type (max u v) :=
  { s : (i : Λ) → (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u) //
    ∀ {i j : Λ} (f : i ⟶ j),
      ((𝒮.bigAffineToScheme S).map (D.map f)).appTop (s j) = s i }

/-- Compatible families of stage global sections form a commutative ring
as an intersection of equalizer subrings for the restriction maps. -/
def limitGlobalSectionsSubring {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S) :
    Subring ((i : Λ) → (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u)) :=
  ⨅ (i : Λ) (j : Λ) (f : i ⟶ j),
    RingHom.eqLocus
      (((𝒮.bigAffineToScheme S).map (D.map f)).appTop.hom.comp
        (Pi.evalRingHom (fun k ↦ Γ((𝒮.bigAffineToScheme S).obj (D.obj k), ⊤)) j))
      (Pi.evalRingHom (fun k ↦ Γ((𝒮.bigAffineToScheme S).obj (D.obj k), ⊤)) i)

/-- The carrier of the equalizer subring is exactly the set of families
compatible under every transition map. -/
theorem limitGlobalSectionsSubring_carrier {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) :
    {s : (i : Λ) → (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u) |
      ∀ {i j : Λ} (f : i ⟶ j),
        ((𝒮.bigAffineToScheme S).map (D.map f)).appTop (s j) = s i} =
      {s | s ∈ limitGlobalSectionsSubring D} := by
  ext s
  simp only [Set.mem_setOf_eq, limitGlobalSectionsSubring, Subring.mem_iInf,
    RingHom.mem_eqLocus, RingHom.comp_apply, Pi.evalRingHom_apply]

/-- Compatible families of stage global sections form a commutative ring
under pointwise operations. -/
instance instCommRingLimitGlobalSections {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) : CommRing (limitGlobalSections D) :=
  Subring.toCommRing ((limitGlobalSectionsSubring D).copy
    {s | ∀ {i j : Λ} (f : i ⟶ j),
      ((𝒮.bigAffineToScheme S).map (D.map f)).appTop (s j) = s i}
    (limitGlobalSectionsSubring_carrier D))

/-- A family of stage global sections belongs to the inverse limit exactly
when it is compatible under every transition map. -/
theorem mem_limitGlobalSections_iff {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    (s : (i : Λ) → (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u)) :
    (∃ p : limitGlobalSections D, p.val = s) ↔
      ∀ {i j : Λ} (f : i ⟶ j),
        ((𝒮.bigAffineToScheme S).map (D.map f)).appTop (s j) = s i := by
  constructor
  · rintro ⟨p, rfl⟩
    exact p.property
  · intro h
    exact ⟨⟨s, h⟩, rfl⟩

/-- Sections in the inverse limit restrict compatibly along the diagram. -/
theorem limitGlobalSections_compatible {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    {D : Λ ⥤ 𝒮.bigAffineSite S} (s : limitGlobalSections D)
    {i j : Λ} (f : i ⟶ j) :
    ((𝒮.bigAffineToScheme S).map (D.map f)).appTop (s.val j) = s.val i :=
  s.property f

/-- Inverse-limit topology on compatible families of global sections, initial
with respect to the discrete topologies on the stage rings `Γ(X_i, ⊤)`. -/
@[reducible] def limitGlobalSectionsTopology {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) :
    TopologicalSpace (limitGlobalSections D) :=
  ⨅ i : Λ,
    TopologicalSpace.induced (fun s : limitGlobalSections D ↦ s.val i)
      (⊥ : TopologicalSpace
        (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u))

/-- `limitGlobalSectionsTopology` is the infimum of the topologies induced by
the discrete topologies along the projections. -/
theorem limitGlobalSectionsTopology_def {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) :
    limitGlobalSectionsTopology D =
      ⨅ i : Λ,
        TopologicalSpace.induced (fun s : limitGlobalSections D ↦ s.val i)
          (⊥ : TopologicalSpace
            (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u)) :=
  rfl

/-- Projection from inverse-limit global sections onto a stage ring. -/
def limitGlobalSections.eval {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S) (i : Λ) :
    limitGlobalSections D →+*
      (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u) where
  toFun s := s.val i
  map_one' := by intros; rfl
  map_mul' := by intros; rfl
  map_zero' := by intros; rfl
  map_add' := by intros; rfl

/-- `limitGlobalSections.eval D i` evaluates a compatible family at stage `i`. -/
theorem limitGlobalSections.eval_apply {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (i : Λ) (s : limitGlobalSections D) :
    limitGlobalSections.eval D i s = s.val i :=
  rfl

/-- Each projection is continuous for the limit topology and the discrete
topology on the stage ring. -/
theorem continuous_eval_limitGlobalSections {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier} {Λ : Type (max u v)} [Preorder Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S) (i : Λ) :
    @Continuous (limitGlobalSections D)
      (Γ((𝒮.bigAffineToScheme S).obj (D.obj i), ⊤) : Type u)
      (limitGlobalSectionsTopology D) ⊥ (limitGlobalSections.eval D i) :=
  sorry

end AlgebraicGeometry
