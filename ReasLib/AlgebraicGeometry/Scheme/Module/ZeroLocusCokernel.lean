module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.RingTheory.Normal.Local
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A]
variable {X : Scheme.{u}}

/-- The additive morphism from constants to the global sections of the zero scheme cut out by `a`
on `X`, using the structure morphism `f : X ⟶ Spec A`. -/
noncomputable def zeroLocusSectionsAdditive
    (f : X ⟶ Spec (.of A)) (a : A) :
    (forget₂ (ModuleCat A) AddCommGrpCat).obj (ModuleCat.of A A) ⟶
      (forget₂ (ModuleCat A) AddCommGrpCat).obj
        (globalSectionsMod
          (Scheme.zeroSchemeι
              (SheafOfModules.unit X.ringCatSheaf)
              (RingedSpace.unitSectionFromTop X.toRingedSpace (globalSectionsMap f a)) ≫ f)
          (SheafOfModules.unit
            (Scheme.zeroScheme
              (SheafOfModules.unit X.ringCatSheaf)
              (RingedSpace.unitSectionFromTop X.toRingedSpace (globalSectionsMap f a))).ringCatSheaf)) :=
  AddCommGrpCat.ofHom
    (globalSectionsMap
      (Scheme.zeroSchemeι
          (SheafOfModules.unit X.ringCatSheaf)
          (RingedSpace.unitSectionFromTop X.toRingedSpace (globalSectionsMap f a)) ≫ f)).toAddMonoidHom

/-- The additive zero-locus sections map is compatible with the scalar actions of `A`. -/
theorem zeroLocusSectionsAdditive_smul
    (f : X ⟶ Spec (.of A)) (a r : A) :
    zeroLocusSectionsAdditive f a ≫
        (globalSectionsMod
          (Scheme.zeroSchemeι
              (SheafOfModules.unit X.ringCatSheaf)
              (RingedSpace.unitSectionFromTop X.toRingedSpace (globalSectionsMap f a)) ≫ f)
          (SheafOfModules.unit
            (Scheme.zeroScheme
              (SheafOfModules.unit X.ringCatSheaf)
              (RingedSpace.unitSectionFromTop X.toRingedSpace (globalSectionsMap f a))).ringCatSheaf)).smul r =
      (ModuleCat.of A A).smul r ≫ zeroLocusSectionsAdditive f a := sorry

/-- The `A`-linear map from constants to the global sections of the zero scheme cut out by `a` on
`X`, using the structure morphism `f : X ⟶ Spec A`. -/
noncomputable def zeroLocusSectionsMap
    (f : X ⟶ Spec (.of A)) (a : A) :
    ModuleCat.of A A ⟶
      globalSectionsMod
        (Scheme.zeroSchemeι
            (SheafOfModules.unit X.ringCatSheaf)
            (RingedSpace.unitSectionFromTop X.toRingedSpace (globalSectionsMap f a)) ≫ f)
        (SheafOfModules.unit
          (Scheme.zeroScheme
            (SheafOfModules.unit X.ringCatSheaf)
            (RingedSpace.unitSectionFromTop X.toRingedSpace (globalSectionsMap f a))).ringCatSheaf) :=
  ModuleCat.homMk (zeroLocusSectionsAdditive f a)
    (fun r ↦ zeroLocusSectionsAdditive_smul f a r)

/-- The `A`-module cokernel of the constants-to-global-sections map on the zero scheme of `a`. -/
noncomputable def zeroLocusCokernel
    (f : X ⟶ Spec (.of A)) (a : A) : ModuleCat A :=
  Limits.cokernel (zeroLocusSectionsMap f a)

/-- The underlying map of `zeroLocusSectionsMap` is the global-sections ring map from the zero
scheme cut out by `a`. -/
theorem zeroLocusSectionsMap_apply
    (f : X ⟶ Spec (.of A)) (a : A) (x : A) :
    zeroLocusSectionsMap f a x =
      globalSectionsMap
        (Scheme.zeroSchemeι
            (SheafOfModules.unit X.ringCatSheaf)
            (RingedSpace.unitSectionFromTop X.toRingedSpace (globalSectionsMap f a)) ≫ f) x := sorry

/-- For a local normal Nagata domain of dimension two and a nonzero element `a`, the `A`-module
cokernel attached to every normal modification has a uniform finite-length bound. -/
@[stacks 0AXJ]
theorem exists_zeroLocusCokernel_length_bound
    [IsLocalRing A] [NagataRing A] [_root_.IsNormalRing A]
    (h_dimension : ringKrullDim A = 2) (a : A) (ha : a ≠ 0) :
    ∃ N : ℕ, ∀ {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsModification f],
      X.isNormal →
        Module.length A (zeroLocusCokernel f a) ≤ (N : ℕ∞) := sorry

end AlgebraicGeometry.Scheme.Hom
