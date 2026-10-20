/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology
public import ReasLib.CategoryTheory.Functor.Exactness.Additive

/-!
# Homology under change of scalars

For a flat map of commutative rings, extension of scalars is bundled as an exact functor.
The generic exact-functor instances then supply preservation of finite limits, finite colimits,
and homology without local instance installation. Restriction of scalars is treated for maps
between arbitrary rings and independent universe levels. This file specializes the canonical
homological-complex comparison isomorphisms to both change-of-scalars functors.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v w u u₁ u₂

namespace ModuleCat

section Extension

variable {R S : Type u} [CommRing R] [CommRing S]

variable {ι : Type w} {c : ComplexShape ι}

/-- The canonical comparison between homology after flat extension of
scalars and extension of the original homology object. -/
@[stacks 09PQ "homology under flat extension of scalars",
  stacks 03B8 "homology under flat extension of scalars"]
noncomputable def extendScalarsHomologyIso
    (f : R →+* S) (hf : f.Flat)
    (K : HomologicalComplex (ModuleCat R) c) (i : ι) :
    (((ModuleCat.extendScalars f).mapHomologicalComplex c).obj K).homology i ≅
      (ModuleCat.extendScalars f).obj (K.homology i) :=
  K.mapHomologyIso (ExtendScalars.exact f hf).obj i

/-- The flat extension-of-scalars homology comparison is natural in morphisms of homological
complexes. -/
@[reassoc]
theorem extendScalarsHomologyIso_hom_naturality
    (f : R →+* S) (hf : f.Flat)
    {K L : HomologicalComplex (ModuleCat R) c} (phi : K ⟶ L) (i : ι) :
    HomologicalComplex.homologyMap
          (((ModuleCat.extendScalars f).mapHomologicalComplex c).map phi) i ≫
        (extendScalarsHomologyIso f hf L i).hom =
      (extendScalarsHomologyIso f hf K i).hom ≫
        (ModuleCat.extendScalars f).map
          (HomologicalComplex.homologyMap phi i) :=
  HomologicalComplex.mapHomologyIso_hom_naturality phi
    (ExtendScalars.exact f hf).obj i

/-- Flat extension of scalars commutes naturally with homology in a fixed degree. -/
@[stacks 09PQ "homology under flat extension of scalars"]
noncomputable def extendScalarsHomologyFunctorIso
    (f : R →+* S) (hf : f.Flat) (c : ComplexShape ι) (i : ι) :
    (ModuleCat.extendScalars f).mapHomologicalComplex c ⋙
        HomologicalComplex.homologyFunctor (ModuleCat S) c i ≅
      HomologicalComplex.homologyFunctor (ModuleCat R) c i ⋙
        ModuleCat.extendScalars f :=
  HomologicalComplex.mapHomologyFunctorIso (ExtendScalars.exact f hf).obj i

/-- The component of the flat extension-of-scalars homology functor isomorphism is the
canonical objectwise comparison. -/
@[simp]
theorem extendScalarsHomologyFunctorIso_app
    (f : R →+* S) (hf : f.Flat) (c : ComplexShape ι) (i : ι)
    (K : HomologicalComplex (ModuleCat R) c) :
    (extendScalarsHomologyFunctorIso f hf c i).app K =
      extendScalarsHomologyIso f hf K i := rfl

end Extension

section Restriction

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]
variable {ι : Type w} {c : ComplexShape ι}

namespace RestrictScalars

/-- Restriction of scalars preserves and reflects zero objects. -/
@[simp]
theorem isZero_obj_iff (f : R →+* S) (M : ModuleCat.{v} S) :
    IsZero ((ModuleCat.restrictScalars f).obj M) ↔ IsZero M := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  rfl

end RestrictScalars

/-- The canonical comparison between homology after restriction of
scalars and restriction of the original homology object. -/
@[stacks 09PQ "homology under restriction of scalars",
  stacks 03B8 "homology under restriction of scalars"]
noncomputable def restrictScalarsHomologyIso
    (f : R →+* S) (K : HomologicalComplex (ModuleCat.{v} S) c) (i : ι) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj K).homology i ≅
      (ModuleCat.restrictScalars f).obj (K.homology i) :=
  K.mapHomologyIso (RestrictScalars.exact f).obj i

/-- The restriction-of-scalars homology comparison is natural in morphisms of homological
complexes. -/
@[reassoc]
theorem restrictScalarsHomologyIso_hom_naturality
    (f : R →+* S) {K L : HomologicalComplex (ModuleCat.{v} S) c}
    (phi : K ⟶ L) (i : ι) :
    HomologicalComplex.homologyMap
          (((ModuleCat.restrictScalars f).mapHomologicalComplex c).map phi) i ≫
        (restrictScalarsHomologyIso f L i).hom =
      (restrictScalarsHomologyIso f K i).hom ≫
        (ModuleCat.restrictScalars f).map
          (HomologicalComplex.homologyMap phi i) :=
  HomologicalComplex.mapHomologyIso_hom_naturality phi
    (RestrictScalars.exact f).obj i

/-- Restriction of scalars commutes naturally with homology in a fixed degree. -/
@[stacks 09PQ "homology under restriction of scalars"]
noncomputable def restrictScalarsHomologyFunctorIso
    (f : R →+* S) (c : ComplexShape ι) (i : ι) :
    (ModuleCat.restrictScalars f).mapHomologicalComplex c ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{v} R) c i ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{v} S) c i ⋙
        ModuleCat.restrictScalars f :=
  HomologicalComplex.mapHomologyFunctorIso (RestrictScalars.exact f).obj i

/-- The component of the restriction-of-scalars homology functor isomorphism is the canonical
objectwise comparison. -/
@[simp]
theorem restrictScalarsHomologyFunctorIso_app
    (f : R →+* S) (c : ComplexShape ι) (i : ι)
    (K : HomologicalComplex (ModuleCat.{v} S) c) :
    (restrictScalarsHomologyFunctorIso f c i).app K =
      restrictScalarsHomologyIso f K i := rfl

/-- Homology in a fixed degree vanishes after restriction of scalars exactly when it vanishes
before restriction. -/
@[simp]
theorem restrictScalarsHomologyIsZero_iff
    (f : R →+* S) (K : HomologicalComplex (ModuleCat.{v} S) c) (i : ι) :
    IsZero ((((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj K).homology i) ↔
      IsZero (K.homology i) :=
  (restrictScalarsHomologyIso f K i).isZero_iff.trans
    (RestrictScalars.isZero_obj_iff f (K.homology i))

/-- A homological complex is acyclic after restriction of scalars exactly when it was acyclic
before restriction. -/
@[simp]
theorem restrictScalars_acyclic_iff
    (f : R →+* S) (K : HomologicalComplex (ModuleCat.{v} S) c) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj K).Acyclic ↔
      K.Acyclic := by
  rw [HomologicalComplex.acyclic_iff, HomologicalComplex.acyclic_iff]
  apply forall_congr'
  intro i
  exact
    (HomologicalComplex.exactAt_iff_isZero_homology
      (K := ((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj K)
      (i := i)).trans
      ((restrictScalarsHomologyIsZero_iff f K i).trans
        (HomologicalComplex.exactAt_iff_isZero_homology
          (K := K) (i := i)).symm)

/-- A chain complex has vanishing homology in every positive degree after restriction of scalars
exactly when it has vanishing positive homology before restriction. -/
@[simp]
theorem restrictScalars_positiveHomologyIsZero_iff
    (f : R →+* S) (K : ChainComplex (ModuleCat.{v} S) ℤ) :
    (∀ n : ℕ+, IsZero
      ((((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.down ℤ)).obj K).homology
        (n : ℤ))) ↔
      ∀ n : ℕ+, IsZero (K.homology (n : ℤ)) :=
  forall_congr' fun n ↦ restrictScalarsHomologyIsZero_iff f K (n : ℤ)

end Restriction

end ModuleCat
