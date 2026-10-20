/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.HodgeFiltration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex ComplexShape
  CochainComplex.Brutal.Stage CategoryTheory.Functor.RightDerived.Homotopy

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}}

/-- Hypercohomology of the brutal truncation of the relative de Rham complex in degree `n`. -/
noncomputable abbrev hodgeSource (f : X ⟶ S) (p n : ℤ) : Type u :=
  @Functor.RightDerived.Homotopy.cochainCohomology
    (RingedSite.ModuleCat.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)) inferInstance
      inferInstance
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (ModuleCat.{u} (RingedSite.Hom.globalSectionsRing
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))) inferInstance inferInstance
      (ModuleCat.hasDerivedCategory (RingedSite.Hom.globalSectionsRing
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)))
    (RingedSite.Hom.moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (RingedSite.Hom.moduleGlobalSectionsFunctor_additive.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (RingedSite.Hom.moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (CochainComplex.Brutal.Stage.obj
      ((RingedSpace.DeRham.complex f.toLRSHom.toShHom).extend embeddingUpNat) p) n

/-- The module-valued cohomology group `H^q(X, Ωᵖ_{X/S})`. -/
noncomputable abbrev hodgeCohomology (f : X ⟶ S) (p q : ℕ) : Type u :=
  @Functor.RightDerived.Homotopy.cochainCohomology
    (RingedSite.ModuleCat.{u} (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)) inferInstance
      inferInstance
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (ModuleCat.{u} (RingedSite.Hom.globalSectionsRing
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))) inferInstance inferInstance
      (ModuleCat.hasDerivedCategory (RingedSite.Hom.globalSectionsRing
        (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)))
    (RingedSite.Hom.moduleGlobalSectionsFunctor.{u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (RingedSite.Hom.moduleGlobalSectionsFunctor_additive.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    (RingedSite.Hom.moduleGlobalSectionsToModuleDerived_hasRightDerivedFunctor.{u, u, u, u}
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom))
    ((CochainComplex.singleFunctor _ (0 : ℤ)).obj
      ((RingedSpace.DeRham.complex f.toLRSHom.toShHom).X p)) q

/-- The carrier of the `p`-th stage of the Hodge filtration in degree `n`. -/
noncomputable abbrev hodgeFiltrationStage (f : X ⟶ S) (n p : ℤ) : Type u :=
  (Subobject.underlying.obj ((hodgeFiltration f n).stage p) :
    ModuleCat.{u} (RingedSite.Hom.globalSectionsRing
      (RingedSpace.DeRham.coefficientSite f.toLRSHom.toShHom)))

/-- Explicit data realizing logarithmic, de Rham, and Hodge first-Chern classes and products. -/
structure ChernClassContext.{v} {X S : Scheme.{v}} (f : X ⟶ S) where
  /-- The cohomology map induced by the logarithmic differential on units. -/
  dlogCohomologyMap : X.PicardGroup →+ hodgeSource f 1 2
  /-- The de Rham first-Chern operation. -/
  deRhamFirstChern : X.PicardGroup →+ cohomology f 2
  /-- The Hodge first-Chern operation. -/
  hodgeFirstChern : X.PicardGroup →+ hodgeCohomology f 1 1
  /-- Projection from truncated hypercohomology to Hodge cohomology. -/
  hodgeProjection : ∀ a : ℕ,
    hodgeSource f (a : ℤ) (2 * (a : ℤ)) →+ hodgeCohomology f a a
  /-- Iterated cup product on truncated hypercohomology classes. -/
  truncatedCupProduct : ∀ {a : ℕ},
    (Fin a → hodgeSource f 1 2) → hodgeSource f (a : ℤ) (2 * (a : ℤ))
  /-- Iterated cup product on relative de Rham cohomology classes. -/
  deRhamCupProduct : ∀ {a : ℕ},
    (Fin a → cohomology f 2) → cohomology f (2 * (a : ℤ))
  /-- Iterated cup product on Hodge cohomology classes. -/
  hodgeCupProduct : ∀ {a : ℕ},
    (Fin a → hodgeCohomology f 1 1) → hodgeCohomology f a a
  /-- The truncated class maps to the de Rham first-Chern class. -/
  hodgeMap_dlog : ∀ x : X.PicardGroup,
    (hodgeMap f 1 2).hom (dlogCohomologyMap x) = deRhamFirstChern x
  /-- Projection of the truncated class gives the Hodge first-Chern class. -/
  hodgeProjection_dlog : ∀ x : X.PicardGroup,
    hodgeProjection 1 (dlogCohomologyMap x) = hodgeFirstChern x
  /-- The Hodge map carries a truncated cup product to the de Rham cup product. -/
  hodgeMap_cup : ∀ {a : ℕ} (x : Fin a → hodgeSource f 1 2),
    (hodgeMap f (a : ℤ) (2 * (a : ℤ))).hom (truncatedCupProduct x) =
      deRhamCupProduct (fun i ↦ (hodgeMap f 1 2).hom (x i))
  /-- Projection carries a truncated cup product to the Hodge cup product. -/
  hodgeProjection_cup : ∀ {a : ℕ} (x : Fin a → hodgeSource f 1 2),
    hodgeProjection a (truncatedCupProduct x) =
      hodgeCupProduct (fun i ↦ hodgeProjection 1 (x i))

namespace ChernClassContext

/-- Construct explicit Chern-class realization data from its maps, operations, and laws. -/
noncomputable def ofMaps {f : X ⟶ S}
    (dlogCohomologyMap : X.PicardGroup →+ hodgeSource f 1 2)
    (deRhamFirstChern : X.PicardGroup →+ cohomology f 2)
    (hodgeFirstChern : X.PicardGroup →+ hodgeCohomology f 1 1)
    (hodgeProjection : ∀ a : ℕ,
      hodgeSource f (a : ℤ) (2 * (a : ℤ)) →+ hodgeCohomology f a a)
    (truncatedCupProduct : ∀ {a : ℕ},
      (Fin a → hodgeSource f 1 2) → hodgeSource f (a : ℤ) (2 * (a : ℤ)))
    (deRhamCupProduct : ∀ {a : ℕ},
      (Fin a → cohomology f 2) → cohomology f (2 * (a : ℤ)))
    (hodgeCupProduct : ∀ {a : ℕ},
      (Fin a → hodgeCohomology f 1 1) → hodgeCohomology f a a)
    (hodgeMap_dlog : ∀ x : X.PicardGroup,
      (hodgeMap f 1 2).hom (dlogCohomologyMap x) = deRhamFirstChern x)
    (hodgeProjection_dlog : ∀ x : X.PicardGroup,
      hodgeProjection 1 (dlogCohomologyMap x) = hodgeFirstChern x)
    (hodgeMap_cup : ∀ {a : ℕ} (x : Fin a → hodgeSource f 1 2),
      (hodgeMap f (a : ℤ) (2 * (a : ℤ))).hom (truncatedCupProduct x) =
        deRhamCupProduct (fun i ↦ (hodgeMap f 1 2).hom (x i)))
    (hodgeProjection_cup : ∀ {a : ℕ} (x : Fin a → hodgeSource f 1 2),
      hodgeProjection a (truncatedCupProduct x) =
        hodgeCupProduct (fun i ↦ hodgeProjection 1 (x i))) :
    ChernClassContext f where
  dlogCohomologyMap := dlogCohomologyMap
  deRhamFirstChern := deRhamFirstChern
  hodgeFirstChern := hodgeFirstChern
  hodgeProjection := hodgeProjection
  truncatedCupProduct := truncatedCupProduct
  deRhamCupProduct := deRhamCupProduct
  hodgeCupProduct := hodgeCupProduct
  hodgeMap_dlog := hodgeMap_dlog
  hodgeProjection_dlog := hodgeProjection_dlog
  hodgeMap_cup := hodgeMap_cup
  hodgeProjection_cup := hodgeProjection_cup

/-- The constructor `ofMaps` records all four defining comparison laws. -/
theorem ofMaps_spec {f : X ⟶ S}
    (dlogCohomologyMap : X.PicardGroup →+ hodgeSource f 1 2)
    (deRhamFirstChern : X.PicardGroup →+ cohomology f 2)
    (hodgeFirstChern : X.PicardGroup →+ hodgeCohomology f 1 1)
    (hodgeProjection : ∀ a : ℕ,
      hodgeSource f (a : ℤ) (2 * (a : ℤ)) →+ hodgeCohomology f a a)
    (truncatedCupProduct : ∀ {a : ℕ},
      (Fin a → hodgeSource f 1 2) → hodgeSource f (a : ℤ) (2 * (a : ℤ)))
    (deRhamCupProduct : ∀ {a : ℕ},
      (Fin a → cohomology f 2) → cohomology f (2 * (a : ℤ)))
    (hodgeCupProduct : ∀ {a : ℕ},
      (Fin a → hodgeCohomology f 1 1) → hodgeCohomology f a a)
    (hodgeMap_dlog : ∀ x : X.PicardGroup,
      (hodgeMap f 1 2).hom (dlogCohomologyMap x) = deRhamFirstChern x)
    (hodgeProjection_dlog : ∀ x : X.PicardGroup,
      hodgeProjection 1 (dlogCohomologyMap x) = hodgeFirstChern x)
    (hodgeMap_cup : ∀ {a : ℕ} (x : Fin a → hodgeSource f 1 2),
      (hodgeMap f (a : ℤ) (2 * (a : ℤ))).hom (truncatedCupProduct x) =
        deRhamCupProduct (fun i ↦ (hodgeMap f 1 2).hom (x i)))
    (hodgeProjection_cup : ∀ {a : ℕ} (x : Fin a → hodgeSource f 1 2),
      hodgeProjection a (truncatedCupProduct x) =
        hodgeCupProduct (fun i ↦ hodgeProjection 1 (x i)))
    (x : X.PicardGroup) {a : ℕ} (y : Fin a → hodgeSource f 1 2) :
    let C := ofMaps dlogCohomologyMap deRhamFirstChern hodgeFirstChern hodgeProjection
      truncatedCupProduct deRhamCupProduct hodgeCupProduct hodgeMap_dlog
      hodgeProjection_dlog hodgeMap_cup hodgeProjection_cup
    (((hodgeMap f 1 2).hom (C.dlogCohomologyMap x) = C.deRhamFirstChern x) ∧
      C.hodgeProjection 1 (C.dlogCohomologyMap x) = C.hodgeFirstChern x) ∧
      (((hodgeMap f (a : ℤ) (2 * (a : ℤ))).hom (C.truncatedCupProduct y) =
          C.deRhamCupProduct (fun i ↦ (hodgeMap f 1 2).hom (y i))) ∧
        C.hodgeProjection a (C.truncatedCupProduct y) =
          C.hodgeCupProduct (fun i ↦ C.hodgeProjection 1 (y i))) := sorry

end ChernClassContext

/-- The logarithmic class of an invertible module is the image of its Picard class. -/
noncomputable def gammaOne (f : X ⟶ S) (C : ChernClassContext f)
    (L : X.Modules) [Scheme.Modules.Invertible L] : hodgeSource f 1 2 :=
  C.dlogCohomologyMap (Scheme.Modules.picardClass L)

/-- The Hodge map sends the logarithmic class to the de Rham first-Chern class. -/
theorem hodgeMap_gammaOne (f : X ⟶ S) (C : ChernClassContext f)
    (L : X.Modules) [Scheme.Modules.Invertible L] :
    (hodgeMap f 1 2).hom (gammaOne f C L) =
      C.deRhamFirstChern (Scheme.Modules.picardClass L) := sorry

/-- Projection of the logarithmic class is the Hodge first-Chern class. -/
theorem hodgeProjection_gammaOne (f : X ⟶ S) (C : ChernClassContext f)
    (L : X.Modules) [Scheme.Modules.Invertible L] :
    C.hodgeProjection 1 (gammaOne f C L) =
      C.hodgeFirstChern (Scheme.Modules.picardClass L) := sorry

/-- The de Rham first-Chern class lies in the first Hodge-filtration stage. -/
theorem deRhamFirstChern_mem_hodgeFiltration (f : X ⟶ S)
    (C : ChernClassContext f) (L : X.Modules) [Scheme.Modules.Invertible L] :
    ∃ z : hodgeFiltrationStage f 2 1,
      ((hodgeFiltration f 2).stage 1).arrow.hom z =
        C.deRhamFirstChern (Scheme.Modules.picardClass L) := sorry

/-- The iterated truncated cup product of logarithmic classes for a finite family. -/
noncomputable def gammaCupProduct (f : X ⟶ S) (C : ChernClassContext f) {a : ℕ}
    (L : Fin a → X.Modules) [∀ i, Scheme.Modules.Invertible (L i)] :
    hodgeSource f (a : ℤ) (2 * (a : ℤ)) :=
  C.truncatedCupProduct (fun i ↦ gammaOne f C (L i))

/-- The Hodge map sends the iterated truncated product to the de Rham product. -/
theorem hodgeMap_gammaCupProduct (f : X ⟶ S) (C : ChernClassContext f) {a : ℕ}
    (L : Fin a → X.Modules) [∀ i, Scheme.Modules.Invertible (L i)] :
    (hodgeMap f (a : ℤ) (2 * (a : ℤ))).hom (gammaCupProduct f C L) =
      C.deRhamCupProduct
        (fun i ↦ C.deRhamFirstChern (Scheme.Modules.picardClass (L i))) := sorry

/-- The iterated de Rham first-Chern product lies in the `a`-th Hodge-filtration stage. -/
theorem deRhamFirstChernCupProduct_mem_hodgeFiltration
    (f : X ⟶ S) (C : ChernClassContext f) {a : ℕ}
    (L : Fin a → X.Modules) [∀ i, Scheme.Modules.Invertible (L i)] :
    ∃ z : hodgeFiltrationStage f (2 * (a : ℤ)) (a : ℤ),
      ((hodgeFiltration f (2 * (a : ℤ))).stage (a : ℤ)).arrow.hom z =
        C.deRhamCupProduct
          (fun i ↦ C.deRhamFirstChern (Scheme.Modules.picardClass (L i))) := sorry

/-- Projection of the iterated truncated product is the iterated Hodge product. -/
theorem hodgeProjection_gammaCupProduct (f : X ⟶ S)
    (C : ChernClassContext f) {a : ℕ}
    (L : Fin a → X.Modules) [∀ i, Scheme.Modules.Invertible (L i)] :
    C.hodgeProjection a (gammaCupProduct f C L) =
      C.hodgeCupProduct
        (fun i ↦ C.hodgeFirstChern (Scheme.Modules.picardClass (L i))) := sorry

end AlgebraicGeometry.Scheme.DeRham
