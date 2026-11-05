/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactRepresentationDuality
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat

noncomputable section

universe u

namespace CompactModule

variable (Λ : Type u) [CommRing Λ] [Finite Λ]

/-- Finite products carry the product topology and pointwise module structure.
This construction does not require character duality or finite coefficients. -/
instance : HasFiniteProducts (CompactModule Λ) where
  out n :=
    { has_limit := fun F ↦ by
        let P : CompactModule Λ :=
          { toModule := ModuleCat.of Λ (∀ i : Fin n, (F.obj ⟨i⟩).toModule) }
        let c : Cone F :=
          { pt := P
            π := Discrete.natTrans (fun i ↦ ContinuousLinearMap.proj i.as) }
        exact HasLimit.mk
          { cone := c
            isLimit :=
              { lift := fun s ↦ ContinuousLinearMap.pi (fun i ↦ s.π.app ⟨i⟩)
                fac := by
                  intro s i
                  apply ContinuousLinearMap.ext
                  intro x
                  rfl
                uniq := by
                  intro s m hm
                  apply ContinuousLinearMap.ext
                  intro x
                  funext i
                  exact congrArg (fun f ↦ CompactModule.linear Λ f x) (hm ⟨i⟩) } } }

instance : ((characterEquivalence Λ).inverse).IsEquivalence :=
  (characterEquivalence Λ).isEquivalence_inverse

/-- The abelian structure is transported along the actual continuous character
equivalence; its preadditive operations remain the pointwise ones above. -/
instance : Abelian (CompactModule Λ) :=
  abelianOfEquivalence (characterEquivalence Λ).inverse

end CompactModule

namespace CompactRepresentation

variable (Λ G : Type u) [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance : Preadditive (Cat Λ G) := inferInstanceAs
  (Preadditive ((continuousAction Λ G).FullSubcategory))

/-- Products use the coordinatewise action, which remains jointly continuous.
Neither finiteness of the coefficients nor continuity of group multiplication
is needed for this construction. -/
instance : HasFiniteProducts (Cat Λ G) where
  out n :=
    { has_limit := fun F ↦ by
        let P : CompactModule Λ :=
          { toModule := ModuleCat.of Λ (∀ i : Fin n, (F.obj ⟨i⟩).obj.V.toModule) }
        let A : Action (CompactModule Λ) G :=
          { V := P
            ρ :=
              { toFun := fun g ↦ ContinuousLinearMap.piMap
                  (fun i ↦ (F.obj ⟨i⟩).obj.ρ g)
                map_one' := by
                  apply ContinuousLinearMap.ext
                  intro x
                  funext i
                  exact congrArg (fun f ↦ CompactModule.linear Λ f (x i))
                    (F.obj ⟨i⟩).obj.ρ.map_one
                map_mul' := by
                  intro g h
                  apply ContinuousLinearMap.ext
                  intro x
                  funext i
                  exact congrArg (fun f ↦ CompactModule.linear Λ f (x i))
                    ((F.obj ⟨i⟩).obj.ρ.map_mul g h) } }
        have hA : continuousAction Λ G A := by
          apply continuous_pi
          intro i
          exact (F.obj ⟨i⟩).property.comp
            (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))
        let c : Cone F :=
          { pt := ⟨A, hA⟩
            π := Discrete.natTrans (fun i ↦ ObjectProperty.homMk
              { hom := ContinuousLinearMap.proj i.as
                comm := by
                  intro g
                  apply ContinuousLinearMap.ext
                  intro x
                  rfl }) }
        exact HasLimit.mk
          { cone := c
            isLimit :=
              { lift := fun s ↦ ObjectProperty.homMk
                  { hom := ContinuousLinearMap.pi (fun i ↦ (s.π.app ⟨i⟩).hom.hom)
                    comm := by
                      intro g
                      apply ContinuousLinearMap.ext
                      intro x
                      funext i
                      exact congrArg (fun f ↦ CompactModule.linear Λ f x)
                        ((s.π.app ⟨i⟩).hom.comm g) }
                fac := by
                  intro s i
                  apply ObjectProperty.hom_ext
                  apply Action.hom_ext
                  apply ContinuousLinearMap.ext
                  intro x
                  rfl
                uniq := by
                  intro s m hm
                  apply ObjectProperty.hom_ext
                  apply Action.hom_ext
                  apply ContinuousLinearMap.ext
                  intro x
                  funext i
                  exact congrArg (fun f ↦ CompactModule.linear Λ f.hom.hom x)
                    (hm ⟨i⟩) } } }

instance : ((equivalence Λ G).inverse).IsEquivalence :=
  (equivalence Λ G).isEquivalence_inverse

instance : Abelian (Cat Λ G) := abelianOfEquivalence (equivalence Λ G).inverse

/-- These projectives are compact duals of ambient injectives, not finite or
all-discrete projective substitutes. -/
theorem dual_projective (M : DiscreteModuleCat Λ G) [Injective M] :
    Projective (dual Λ G M) := by sorry

end CompactRepresentation
