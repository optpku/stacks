/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification.ReductionPossible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul
open AlgebraicGeometry.Scheme.ModuleDerived.InternalHom
open AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex
open RingedSpace.Module.Derived

universe u

namespace RationalSingularity

/- Lemma 54.8.8: for a two-dimensional local normal Nagata domain with a dualizing module,
uniform annihilation of the cokernels of normalized duality trace maps from normal
modifications implies that reduction to rational singularities is possible. -/
@[stacks 0B4S] #check
  (RationalSingularity.ofTraceCokernelAnnihilatedBy :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [NagataRing A]
    [IsNormalRing A] (h_dimension : ringKrullDim A = 2)
    (ωA : ModuleCat.{u} A)
    (hωA : ModuleCat.IsDualizingModule ωA)
    (d : A) (hd : d ≠ 0)
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (h_trace : ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsModification f],
      (h_normal : X.isNormal) →
        ∀ [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
          (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)),
        ∃ (hX : IsLocallyNoetherian X) (ωX : X.Modules)
          (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
          (hωS : ωS.IsDualizingComplex HS)
          (hωS_affine :
            IsIsomorphic ωS
              ((affineDerivedTilde A).obj ((ModuleCat.single0 ωA)⟦(2 : ℤ)⟧)))
          (hωX : @Scheme.IsDualizingModule X hX ωX)
          (h_relative :
            @RelativeTo (Spec (CommRingCat.of A)) X inferInstance f inferInstance
              inferInstance HS inferInstance HX ωS hωS
              (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
          (normalizedDualizingTrace :
            (RingedSpace.moduleDerivedPushforward f.toShHom).obj
              (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧) ⟶ ωS)
          (a : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace ⥤
            RingedSpace.ModuleDerived X.toRingedSpace)
          (aAdjunction : RingedSpace.moduleDerivedPushforward f.toShHom ⊣ a)
          (e : a.obj ωS ≅
            (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧))
          (h_normalizedDualizingTrace :
            normalizedDualizingTrace =
              (RingedSpace.moduleDerivedPushforward f.toShHom).map e.inv ≫
                aAdjunction.counit.app ωS)
          (sourceGlobalSectionsComparison :
            Scheme.Hom.globalSectionsMod f ωX ≅
              (IsRationalSingularity.dualizingGlobalSectionsFunctor A).obj
                ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
                  (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)))
          (targetGlobalSectionsComparison :
            (IsRationalSingularity.dualizingGlobalSectionsFunctor A).obj ωS ≅ ωA)
          (τ : Scheme.Hom.globalSectionsMod f ωX ⟶ ωA),
          τ = sourceGlobalSectionsComparison.hom ≫
              (IsRationalSingularity.dualizingGlobalSectionsFunctor A).map
                normalizedDualizingTrace ≫
              targetGlobalSectionsComparison.hom ∧
            d ∈ Module.annihilator A
              (Limits.cokernel τ : ModuleCat.{u} A)),
    ReductionPossible A)

end RationalSingularity
