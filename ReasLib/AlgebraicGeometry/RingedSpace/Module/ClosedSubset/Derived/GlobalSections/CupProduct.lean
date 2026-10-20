/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor.Bifunctor
public import ReasLib.CategoryTheory.Monoidal.CohomologyProduct
import Mathlib.CategoryTheory.CommSq
import Mathlib.Tactic.CrossRefAttribute

/-!
# Supported cup products on derived global sections

This leaf owns the source-independent interface used by the closed-support cup product.  The
supported morphism and its ambient realization are concrete fields; only compatibility equations
are propositions.  A geometric construction can fill the fields using the relative adjunction and
`Adjunction.supportTensorOfFunctors` (or a specialized mate producer), while downstream results need
only this model and its specification.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open ModuleDerived.Tensor
open scoped RingedSpaceTensor
open scoped RingedSpaceDerivedGlobalSections
open scoped RingedSpaceClosedSupport

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport

variable {X : RingedSpace.{u}}
variable [ModuleDerived.Tensor.Has X]

/-- Forget support in the second input of the global-sections pairing. -/
@[stacks 0G76 "forget support in a global-sections input pair"]
noncomputable def pairForget (Z : TopologicalSpace.Closeds X) :
    Functor.prod (RΓ(X)) (RΓₛ[Z]) ⟶ Functor.prod (RΓ(X)) (RΓ(X)) :=
  NatTrans.prod (𝟙 (RΓ(X))) (forgetDerived X Z)

/-- An object-level supported cup-product realization.  The natural family owner is
`SupportedCupProduct`; this bridge is useful once `K` and `M` have been fixed. -/
@[stacks 0G76 "supported cup-product model"]
structure CupProductModel (Z : TopologicalSpace.Closeds X)
    (K M : AlgebraicGeometry.RingedSpace.ModuleDerived X) where
  /-- The cup-product morphism with support in `Z`. -/
  map :
    globalSectionsObj X ((RΓ(X)).obj K) ((RΓₛ[Z]).obj M) ⟶
      (RΓₛ[Z]).obj (K ⊗ᴸ M)
  /-- The same source map written in the iterated ambient global-sections model. -/
  ambientMap :
    globalSectionsObj X ((RΓ(X)).obj K) ((RΓₛ[Z]).obj M) ⟶
      (ambientModel X Z).obj (K ⊗ᴸ M)
  /-- The supported map is realized by the canonical ambient comparison. -/
  realizes :
    map ≫ (ambientComparison X Z).app (K ⊗ᴸ M) = ambientMap

/-- A natural supported cup-product family together with its ambient realization and ordinary
global cup product.  The morphism fields are concrete natural transformations; the remaining
fields are the realization and forget-support compatibility propositions. -/
@[stacks 0G76 "supported cup-product family"]
structure SupportedCupProduct (Z : TopologicalSpace.Closeds X) where
  /-- The supported cup-product natural transformation. -/
  map :
    Functor.prod (RΓ(X)) (RΓₛ[Z]) ⋙ globalSectionsFunctor X ⟶
      ModuleDerived.Tensor.functor X ⋙ (RΓₛ[Z])
  /-- The same family in the ambient iterated global-sections model. -/
  ambientMap :
    Functor.prod (RΓ(X)) (RΓₛ[Z]) ⋙ globalSectionsFunctor X ⟶
      ModuleDerived.Tensor.functor X ⋙ ambientModel X Z
  /-- The supported family is realized by the canonical ambient comparison. -/
  realizes :
    map ≫ Functor.whiskerLeft
      (ModuleDerived.Tensor.functor X)
      (ambientComparison X Z) = ambientMap
  /-- The ordinary global cup-product natural transformation. -/
  globalMap :
    Functor.prod (RΓ(X)) (RΓ(X)) ⋙ globalSectionsFunctor X ⟶
      ModuleDerived.Tensor.functor X ⋙ (RΓ(X))
  /-- The ambient model and ordinary cup products commute with forgetting support. -/
  forget_comm :
    ambientMap ≫ Functor.whiskerLeft
        (ModuleDerived.Tensor.functor X) (ambientForget X Z) =
      Functor.whiskerRight (pairForget Z) (globalSectionsFunctor X) ≫ globalMap

/-- Build a supported cup-product family from its natural transformations and compatibility laws. -/
@[stacks 0G76 "supported cup-product family constructor"]
def SupportedCupProduct.ofMaps
    (map :
      Functor.prod (RΓ(X)) (RΓₛ[Z]) ⋙ globalSectionsFunctor X ⟶
        ModuleDerived.Tensor.functor X ⋙ (RΓₛ[Z]))
    (ambientMap :
      Functor.prod (RΓ(X)) (RΓₛ[Z]) ⋙ globalSectionsFunctor X ⟶
        ModuleDerived.Tensor.functor X ⋙ ambientModel X Z)
    (hrealizes :
      map ≫ Functor.whiskerLeft
        (ModuleDerived.Tensor.functor X)
        (ambientComparison X Z) = ambientMap)
    (globalMap :
      Functor.prod (RΓ(X)) (RΓ(X)) ⋙ globalSectionsFunctor X ⟶
        ModuleDerived.Tensor.functor X ⋙ (RΓ(X)))
    (hforget :
      ambientMap ≫ Functor.whiskerLeft
          (ModuleDerived.Tensor.functor X) (ambientForget X Z) =
        Functor.whiskerRight (pairForget Z) (globalSectionsFunctor X) ≫ globalMap) :
    SupportedCupProduct Z :=
  { map := map
    ambientMap := ambientMap
    realizes := hrealizes
    globalMap := globalMap
    forget_comm := hforget }

/-- Build the supported component of a family from its ambient realization and an explicitly
supplied comparison isomorphism.  Keeping the isomorphism as data prevents a deferred `IsIso`
proof from selecting the public cup-product morphism. -/
@[stacks 0G76 "supported cup-product family from ambient maps"]
noncomputable def SupportedCupProduct.ofAmbient
    (e : derived X Z ≅ ambientModel X Z)
    (he : e.hom = ambientComparison X Z)
    (ambientMap :
      Functor.prod (RΓ(X)) (RΓₛ[Z]) ⋙ globalSectionsFunctor X ⟶
        ModuleDerived.Tensor.functor X ⋙ ambientModel X Z)
    (globalMap :
      Functor.prod (RΓ(X)) (RΓ(X)) ⋙ globalSectionsFunctor X ⟶
        ModuleDerived.Tensor.functor X ⋙ (RΓ(X)))
    (hforget :
      ambientMap ≫ Functor.whiskerLeft
          (ModuleDerived.Tensor.functor X) (ambientForget X Z) =
        Functor.whiskerRight (pairForget Z) (globalSectionsFunctor X) ≫ globalMap) :
    SupportedCupProduct Z :=
  { map := ambientMap ≫ Functor.whiskerLeft
      (ModuleDerived.Tensor.functor X)
      e.inv
    ambientMap := ambientMap
    realizes := sorry
    globalMap := globalMap
    forget_comm := hforget }

/-- The supported natural transformation selected by `SupportedCupProduct.ofAmbient`. -/
@[stacks 0G76 "supported cup-product family ambient-map specification"]
theorem SupportedCupProduct.ofAmbient_map
    (e : derived X Z ≅ ambientModel X Z)
    (he : e.hom = ambientComparison X Z)
    (ambientMap :
      Functor.prod (RΓ(X)) (RΓₛ[Z]) ⋙ globalSectionsFunctor X ⟶
        ModuleDerived.Tensor.functor X ⋙ ambientModel X Z)
    (globalMap :
      Functor.prod (RΓ(X)) (RΓ(X)) ⋙ globalSectionsFunctor X ⟶
        ModuleDerived.Tensor.functor X ⋙ (RΓ(X)))
    (hforget :
      ambientMap ≫ Functor.whiskerLeft
          (ModuleDerived.Tensor.functor X) (ambientForget X Z) =
        Functor.whiskerRight (pairForget Z) (globalSectionsFunctor X) ≫ globalMap) :
    (SupportedCupProduct.ofAmbient e he ambientMap globalMap hforget).map =
      ambientMap ≫ Functor.whiskerLeft
        (ModuleDerived.Tensor.functor X)
        e.inv := sorry

/-- The component realization equation of a supported cup-product family. -/
@[stacks 0G76 "supported cup-product family realization component"]
theorem SupportedCupProduct.realizes_app
    (P : SupportedCupProduct Z) (K M : AlgebraicGeometry.RingedSpace.ModuleDerived X) :
    P.map.app (K, M) ≫ (ambientComparison X Z).app
      ((ModuleDerived.Tensor.functor X).obj (K, M)) =
      P.ambientMap.app (K, M) := sorry

/-- Forget a supported cup-product family to the object-level realization used by local bridges. -/
@[stacks 0G76 "supported cup-product family object model"]
def SupportedCupProduct.model
    (P : SupportedCupProduct Z)
    (K M : AlgebraicGeometry.RingedSpace.ModuleDerived X) :
    CupProductModel Z K M :=
  { map := P.map.app (K, M)
    ambientMap := P.ambientMap.app (K, M)
    realizes := P.realizes_app K M }

/-- Build a supported cup-product model from its two maps and the ambient realization equation. -/
@[stacks 0G76 "supported cup-product model constructor"]
def CupProductModel.ofMaps
    (map :
      globalSectionsObj X ((RΓ(X)).obj K) ((RΓₛ[Z]).obj M) ⟶
        (RΓₛ[Z]).obj (K ⊗ᴸ M))
    (ambientMap :
      globalSectionsObj X ((RΓ(X)).obj K) ((RΓₛ[Z]).obj M) ⟶
        (ambientModel X Z).obj (K ⊗ᴸ M))
    (hrealizes : map ≫ (ambientComparison X Z).app (K ⊗ᴸ M) = ambientMap) :
    CupProductModel Z K M :=
  { map := map, ambientMap := ambientMap, realizes := hrealizes }

/-- Build an object-level supported cup-product model from its ambient map and an explicit
comparison isomorphism. -/
@[stacks 0G76 "supported cup-product model from ambient map"]
noncomputable def CupProductModel.ofAmbient
    (e : derived X Z ≅ ambientModel X Z)
    (he : e.hom = ambientComparison X Z)
    (ambientMap :
      globalSectionsObj X ((RΓ(X)).obj K) ((RΓₛ[Z]).obj M) ⟶
        (ambientModel X Z).obj (K ⊗ᴸ M)) :
    CupProductModel Z K M :=
  { map := ambientMap ≫ e.inv.app (K ⊗ᴸ M)
    ambientMap := ambientMap
    realizes := sorry }

/-- The supported map selected by `CupProductModel.ofAmbient`. -/
@[stacks 0G76 "supported cup-product model ambient-map specification"]
theorem CupProductModel.ofAmbient_map
    (e : derived X Z ≅ ambientModel X Z)
    (he : e.hom = ambientComparison X Z)
    (ambientMap :
      globalSectionsObj X ((RΓ(X)).obj K) ((RΓₛ[Z]).obj M) ⟶
        (ambientModel X Z).obj (K ⊗ᴸ M)) :
    (CupProductModel.ofAmbient e he ambientMap).map =
      ambientMap ≫ e.inv.app (K ⊗ᴸ M) := sorry

/-- The ambient realization of a supported cup product satisfies the forget-support square. -/
@[stacks 0G76 "supported cup-product forget-support square condition"]
def forgetCommSq
    (P : CupProductModel Z K M)
    (global :
      globalSectionsObj X ((RΓ(X)).obj K) ((RΓ(X)).obj M) ⟶
        (RΓ(X)).obj (K ⊗ᴸ M)) : Prop :=
  CommSq P.ambientMap
    (globalSectionsMap X (𝟙 ((RΓ(X)).obj K)) ((forgetDerived X Z).app M))
    ((ambientForget X Z).app (K ⊗ᴸ M))
    global

/-- The model-side forget-support square of a family, viewed through its object-level bridge. -/
@[stacks 0G76 "supported cup-product family model square"]
theorem SupportedCupProduct.forget_spec
    (P : SupportedCupProduct Z) (K M : AlgebraicGeometry.RingedSpace.ModuleDerived X) :
    forgetCommSq (P.model K M) (P.globalMap.app (K, M)) := sorry

/-- The derived supported cup product commutes with forgetting support.  This is the
family-level square from which degreewise cohomology statements are obtained. -/
@[stacks 0G76 "supported derived cup-product commuting square"]
theorem SupportedCupProduct.derivedCommSq
    (P : SupportedCupProduct Z)
    (K M : AlgebraicGeometry.RingedSpace.ModuleDerived X) :
    CommSq
      (P.map.app (K, M))
      (globalSectionsMap X (𝟙 ((RΓ(X)).obj K)) ((forgetDerived X Z).app M))
      ((forgetDerived X Z).app (K ⊗ᴸ M))
      (P.globalMap.app (K, M)) := sorry

/-- A supported cup-product family transports an ordinary graded cohomology-product square through
forgetting support.  The generic graded pairing transports `derivedCommSq` to cohomology. -/
@[stacks 0G77 "supported cohomology product commuting square"]
theorem SupportedCupProduct.cohomologyCommSq
    (P : SupportedCupProduct Z)
    (product :
      CohomologyProduct
        (fun n : ℤ => globalSectionsHomology X n)
        (globalSectionsFunctor X)
        (MonoidalCategory.tensor (ModuleCat (globalSectionsRing X))))
    (i j : ℤ) (K M : AlgebraicGeometry.RingedSpace.ModuleDerived X) :
    CommSq
      (product.map i j ((RΓ(X)).obj K) ((RΓₛ[Z]).obj M) (P.map.app (K, M)))
      ((MonoidalCategory.tensor (ModuleCat (globalSectionsRing X))).map
        (Prod.mkHom
          (𝟙 ((globalSectionsHomology X i).obj ((RΓ(X)).obj K)))
          ((globalSectionsHomology X j).map ((forgetDerived X Z).app M))))
      ((globalSectionsHomology X (i + j)).map
        ((forgetDerived X Z).app (K ⊗ᴸ M)))
      (product.map i j ((RΓ(X)).obj K) ((RΓ(X)).obj M)
        (P.globalMap.app (K, M))) := sorry

/-- A realized supported cup product induces the derived forget-support square. -/
@[stacks 0G76 "supported cup-product forget-support square"]
theorem map_commSq_of_forget
    (P : CupProductModel Z K M)
    (global :
      globalSectionsObj X ((RΓ(X)).obj K) ((RΓ(X)).obj M) ⟶
        (RΓ(X)).obj (K ⊗ᴸ M))
    (hglobal : forgetCommSq P global) :
    CommSq P.map
      (globalSectionsMap X (𝟙 ((RΓ(X)).obj K)) ((forgetDerived X Z).app M))
      ((forgetDerived X Z).app (K ⊗ᴸ M))
      global := sorry

end AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport
