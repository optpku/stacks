/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Maps
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Dualizing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification.Dualizing
public import ReasLib.RingTheory.Normal.ReductionPossible

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.ModuleDerived.InternalHom
open AlgebraicGeometry.Scheme.Hom.NormalizedDualizingComplex
open RingedSpace.Module.Derived

universe u

namespace RationalSingularity

/-- A uniform annihilator for normalized trace cokernels on normal modifications implies that
reduction to rational singularities is possible for a two-dimensional local normal Nagata domain
with a dualizing complex. -/
theorem ofTraceCokernelAnnihilatedBy
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [NagataRing A]
    [IsNormalRing A] (h_dimension : ringKrullDim A = 2)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (HA : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ωAComplex : DerivedCategory (ModuleCat.{u} A))
    (hωA : ωAComplex.IsDualizingComplex HA)
    (ωA : ModuleCat.{u} A)
    (d : A) (hd : d ≠ 0)
    [MonoidalCategory
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)]
    (HS : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace))
    (canonicalGlobalSectionsFunctor :
      RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace ⥤ ModuleCat.{u} A)
    (h_canonicalGlobalSectionsFunctor :
      canonicalGlobalSectionsFunctor =
        GlobalSections.functor
            (Spec (CommRingCat.of A)).toRingedSpace ⋙
          DerivedCategory.homologyFunctor
            (ModuleCat (Scheme.globalSectionsRing (Spec (CommRingCat.of A)))) 0 ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    (h_trace : ∀ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) [IsModification f],
      (h_normal : X.isNormal) →
        ∀ [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
          (HX : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)),
        ∃ (hX : IsLocallyNoetherian X) (ωX : X.Modules)
          (ωS : RingedSpace.ModuleDerived (Spec (CommRingCat.of A)).toRingedSpace)
          (hωS : ωS.IsDualizingComplex HS)
          (hωS_affine :
            IsIsomorphic ωS
              ((affineTildeDerived A).obj (ωAComplex⟦(2 : ℤ)⟧)))
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
              canonicalGlobalSectionsFunctor.obj
                ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
                  (((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦(2 : ℤ)⟧)))
          (targetGlobalSectionsComparison :
            canonicalGlobalSectionsFunctor.obj ωS ≅ ωA)
          (τ : Scheme.Hom.globalSectionsMod f ωX ⟶ ωA),
          τ = sourceGlobalSectionsComparison.hom ≫
              canonicalGlobalSectionsFunctor.map normalizedDualizingTrace ≫
              targetGlobalSectionsComparison.hom ∧
            d ∈ Module.annihilator A
              (Limits.cokernel τ : ModuleCat.{u} A)) :
    ReductionPossible A := sorry

end RationalSingularity
