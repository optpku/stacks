/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Sections.Comparison
public import ReasLib.Algebra.Category.ModuleCat.Topology.Limit
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Scheme Scheme.Modules SheafOfModules
open Scheme.Opens

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The inverse system `n ↦ sectionsLimit S F / S.I ^ n sectionsLimit S F`. -/
noncomputable def sectionsQuotientSystem (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
  SequentialInverseSystem (ModuleCat A) :=
  @Functor.ofOpSequence (ModuleCat A) inferInstance
    (fun n ↦ Ideal.PowerQuotient.stage S.I (sectionsLimit S F) n) (fun n ↦
    ModuleCat.ofHom
      (AdicCompletion.transitionMap S.I (sectionsLimit S F) (Nat.le_succ n)))

/-- The object at stage `n` of `sectionsQuotientSystem S F` is the exact quotient
`sectionsLimit S F / S.I ^ n sectionsLimit S F`. -/
theorem sectionsQuotientSystem_obj (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (n : ℕ) :
    (sectionsQuotientSystem S F).obj (op n) =
      Ideal.PowerQuotient.stage S.I (sectionsLimit S F) n := rfl

/-- The successor map of `sectionsQuotientSystem S F` is the canonical map from
the exponent `n + 1` quotient to the exponent `n` quotient. -/
theorem sectionsQuotientSystem_stepMap (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (n : ℕ) :
    (sectionsQuotientSystem S F).stepMap n =
      ModuleCat.ofHom
        (AdicCompletion.transitionMap S.I (sectionsLimit S F) (Nat.le_succ n)) := by
  exact Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The system of restrictions to `S.U` of the associated sheaves of the quotients
`sectionsLimit S F / S.I ^ n sectionsLimit S F`. -/
noncomputable def restrictedSectionsQuotientSystem (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
    SequentialInverseSystem (Modules S.U.toScheme) :=
  sectionsQuotientSystem S F ⋙
    tilde.functor (CommRingCat.of A) ⋙
    Scheme.Modules.pullback S.U.ι

/-- The object at stage `n` of `restrictedSectionsQuotientSystem S F` is the
restriction to `S.U` of the tilde sheaf of the exact exponent `n` quotient. -/
theorem restrictedSectionsQuotientSystem_obj (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (n : ℕ) :
    (restrictedSectionsQuotientSystem S F).obj (op n) =
      (Scheme.Modules.pullback S.U.ι).obj
        (tilde (Ideal.PowerQuotient.stage S.I (sectionsLimit S F) n)) := rfl

/-- Every stage of the restricted associated quotient-sheaf system is coherent when the limit topology agrees with its
the `S.I`-adic topology.
The restricted associated quotient sheaves are coherent. -/
theorem restrictedSectionsQuotientSystem_isCoherent
    (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F)) (n : ℕ) :
    ((restrictedSectionsQuotientSystem S F).obj (op n)).IsCoherent := sorry

/-- The quotient-sheaf system regarded as a system of coherent modules under the
equality of the limit and `S.I`-adic topologies. -/
noncomputable def coherentSectionsQuotientSystem (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F)) :
    SequentialInverseSystem
      (RingedSpace.Coh (toScheme S.U).toRingedSpace) :=
  (isCoherent _).lift
    (restrictedSectionsQuotientSystem S F)
    (fun n ↦ restrictedSectionsQuotientSystem_isCoherent S F h_topology n.unop)

/-- Forgetting coherence from stage `n` of `coherentSectionsQuotientSystem`
recovers stage `n` of `restrictedSectionsQuotientSystem`. -/
theorem coherentSectionsQuotientSystem_obj (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F)) (n : ℕ) :
    ((coherentSectionsQuotientSystem S F h_topology).obj (op n)).obj =
      (restrictedSectionsQuotientSystem S F).obj (op n) := rfl

/-- The canonical quotient-stage comparison maps commute with adjacent transition maps
after passing to coherent modules on `S.U`. -/
theorem coherentSectionsComparison_naturality (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F)) (n : ℕ) :
    (coherentSectionsQuotientSystem S F h_topology).stepMap n ≫
        ObjectProperty.homMk (sectionsComparison S F n) =
      ObjectProperty.homMk (sectionsComparison S F (n + 1)) ≫
        F.obj.stepMap n := by
  apply ObjectProperty.hom_ext
  change (Scheme.Modules.pullback S.U.ι).map
      ((tilde.functor (CommRingCat.of A)).map ((sectionsQuotientSystem S F).stepMap n)) ≫
        sectionsComparison S F n =
      sectionsComparison S F (n + 1) ≫ (F.obj.stepMap n).hom
  rw [sectionsQuotientSystem_stepMap]
  let adj := (tilde.adjunction (R := CommRingCat.of A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction S.U.ι)
  apply adj.homEquiv_naturality_right_square
  change ModuleCat.ofHom
      (AdicCompletion.transitionMap S.I (sectionsLimit S F) (Nat.le_succ n)) ≫
        sectionsQuotientProjection S F n =
      sectionsQuotientProjection S F (n + 1) ≫ (sectionsSystem S F).stepMap n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro x
  change (limit.π (sectionsSystem S F) (op n)).hom x =
    ((sectionsSystem S F).stepMap n).hom
      ((limit.π (sectionsSystem S F) (op (n + 1))).hom x)
  exact congrArg (fun f : sectionsLimit S F ⟶ (sectionsSystem S F).obj (op n) ↦ f.hom x)
    (limit.w (sectionsSystem S F) (homOfLE (Nat.le_succ n)).op).symm

/-- The canonical map from the coherent quotient-sheaf system to the given coherent
formal-module system. -/
noncomputable def coherentSectionsComparison (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F)) :
    coherentSectionsQuotientSystem S F h_topology ⟶ F.obj :=
  NatTrans.ofOpSequence (fun n ↦ ObjectProperty.homMk (sectionsComparison S F n))
    (coherentSectionsComparison_naturality S F h_topology)

/-- The component of `coherentSectionsComparison` at stage `n` is the canonical
quotient-stage comparison map, lifted to coherent modules. -/
theorem coherentSectionsComparison_app (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F)) (n : ℕ) :
    (coherentSectionsComparison S F h_topology).app (op n) =
      ObjectProperty.homMk (sectionsComparison S F n) := rfl

/-- Under the topology hypothesis, the coherent quotient-sheaf system satisfies the
ideal-power compatibility conditions of a coherent formal module. -/
theorem coherentSectionsQuotientSystem_mem (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F)) :
    Scheme.IsCoherentFormalModuleSystem
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)
      (coherentSectionsQuotientSystem S F h_topology) := sorry

/-- The coherent formal module represented by the restricted associated sheaves
`(sectionsLimit S F / S.I ^ n sectionsLimit S F)˜|_U`. -/
noncomputable def sectionsQuotientFormalModule (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F)) :
    CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) :=
  ⟨coherentSectionsQuotientSystem S F h_topology,
    coherentSectionsQuotientSystem_mem S F h_topology⟩

/-- The underlying coherent inverse system of `sectionsQuotientFormalModule` is
`coherentSectionsQuotientSystem`. -/
theorem sectionsQuotientFormalModule_obj (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F)) :
    (sectionsQuotientFormalModule S F h_topology).obj =
      coherentSectionsQuotientSystem S F h_topology := rfl

/-- The canonical morphism of coherent formal modules whose stage `n` is the map
`(sectionsLimit S F / S.I ^ n sectionsLimit S F)˜|_U ⟶ Fₙ`. -/
noncomputable def sectionsComparisonHom (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F)) :
    sectionsQuotientFormalModule S F h_topology ⟶ F :=
  ObjectProperty.homMk (coherentSectionsComparison S F h_topology)

/-- After forgetting the coherent-formal-module layer, the component of
`sectionsComparisonHom` at stage `n` is the corresponding component of
`coherentSectionsComparison`. -/
theorem sectionsComparisonHom_app (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F)) (n : ℕ) :
    (sectionsComparisonHom S F h_topology).hom.app (op n) =
      (coherentSectionsComparison S F h_topology).app (op n) := rfl

/-- The canonical comparison morphism is a monomorphism in the abelian category of
coherent formal modules on `S.U` when the limit topology agrees with the `S.I`-adic topology. -/
theorem sectionsComparisonHom_mono (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (h_topology : Functor.limitTopology (sectionsSystem S F) =
      Ideal.adicModuleTopology S.I (sectionsLimit S F)) :
    Mono (sectionsComparisonHom S F h_topology) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
