/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FiniteDual
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CompactSupport.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NewUpperShriek.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport

open Scheme.FiniteTypeSeparatedOver


/-- Derived internal Hom into the normalized relative dualizing complex selected by a new
upper-shriek assignment. -/
noncomputable def dualObject {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    (D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) :
    Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf] :=
  (@Scheme.IsDualizingComplex.boundedDuality U.obj.left inferInstance
      (D.monoidal (toFiniteTypeOver U)) (D.braided (toFiniteTypeOver U))
      (D.closed (toFiniteTypeOver U)) (D.omega (toFiniteTypeOver U)).obj.obj
      (D.dualizing (toFiniteTypeOver U)) inferInstance).obj (op K)

/-- The underlying bounded coherent object of `dualObject` is the value of normalized
bounded duality on `K`. -/
theorem dualObject_def {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    (D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) :
    dualObject D U K =
      (@Scheme.IsDualizingComplex.boundedDuality U.obj.left inferInstance
        (D.monoidal (toFiniteTypeOver U)) (D.braided (toFiniteTypeOver U))
        (D.closed (toFiniteTypeOver U)) (D.omega (toFiniteTypeOver U)).obj.obj
        (D.dualizing (toFiniteTypeOver U)) inferInstance).obj (op K) := sorry

/-- Presentation data used in the compact-support duality argument: a compact-support
presentation of `RHom(K, ωU/k)`, a finite-stage presentation of ordinary cohomology, and
the proper-duality identification between their stage systems. -/
structure DualityPresentation {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    (D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) where
  /-- A compact-support presentation of the dual complex on `U`. -/
  compactSystem : PNatInverseSystem
    Dᵇ[SheafOfModules.isCoherent
      (Over.left (base (Spec (CommRingCat.of k))).obj).ringCatSheaf]
  /-- The chosen inverse system presents compact support of the normalized dual of `K`. -/
  isCompactPresentation :
    IsPresentation (toBase U) (dualObject D U K) compactSystem
  /-- A finite-stage direct system presenting ordinary cohomology of `K`. -/
  ordinarySystem : ℕ+ ⥤ ModuleCat.{u} k
  /-- The colimit of the finite-stage system is ordinary degree-`i` cohomology of `K`. -/
  ordinaryComparison : colimit ordinarySystem ≅ Cohomology.overField (Over.hom U.obj) K i
  /-- Proper duality identifies the compact-support stages with the dual ordinary stages. -/
  stageDuality :
    cohomologyDiagram (Over.hom (base (Spec (CommRingCat.of k))).obj) compactSystem (-i) ≅
      FiniteDual.diagram ordinarySystem
  /-- Every ordinary stage is finite-dimensional over the ground field. -/
  stageFinite : ∀ n, FiniteDimensional k (ordinarySystem.obj n)

/-- A morphism between duality presentations over `f : K ⟶ L`, carrying the
contravariant compact-support system and the covariant ordinary-cohomology system. -/
structure DualityPresentation.Hom {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    {U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k))}
    {K L : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]}
    (f : K ⟶ L) (i : ℤ) (Pₖ : DualityPresentation D U K i)
    (Pₗ : DualityPresentation D U L i) where
  /-- The map of compact-support systems induced contravariantly by `f`. -/
  compactMap : Pₗ.compactSystem ⟶ Pₖ.compactSystem
  /-- The map of finite-stage ordinary-cohomology systems induced by `f`. -/
  ordinaryMap : Pₖ.ordinarySystem ⟶ Pₗ.ordinarySystem
  /-- The ordinary comparison commutes with the map induced by `f`. -/
  ordinary_naturality :
    colimMap ordinaryMap ≫ Pₗ.ordinaryComparison.hom =
      Pₖ.ordinaryComparison.hom ≫
        (Cohomology.overFieldFunctor (Over.hom U.obj) i).map f
  /-- Stagewise proper duality commutes with the maps induced by `f`. -/
  stage_naturality :
    Pₗ.stageDuality.hom ≫ FiniteDual.diagramMap ordinaryMap =
      Functor.whiskerRight compactMap
          (Cohomology.overFieldFunctor
            (Over.hom (base (Spec (CommRingCat.of k))).obj) (-i)) ≫
        Pₖ.stageDuality.hom

/-- Assemble a compact-support duality presentation from its presentation system,
ordinary cohomology system, comparison isomorphisms, and finite-dimensionality proofs. -/
noncomputable def DualityPresentation.ofSystems {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    {U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k))}
    {K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]} {i : ℤ}
    (compactSystem : PNatInverseSystem
      Dᵇ[SheafOfModules.isCoherent
        (Over.left (base (Spec (CommRingCat.of k))).obj).ringCatSheaf])
    (isCompactPresentation : IsPresentation (toBase U) (dualObject D U K) compactSystem)
    (ordinarySystem : ℕ+ ⥤ ModuleCat.{u} k)
    (ordinaryComparison : colimit ordinarySystem ≅
      Cohomology.overField (Over.hom U.obj) K i)
    (stageDuality :
      cohomologyDiagram (Over.hom (base (Spec (CommRingCat.of k))).obj)
        compactSystem (-i) ≅
        FiniteDual.diagram ordinarySystem)
    (stageFinite : ∀ n, FiniteDimensional k (ordinarySystem.obj n)) :
    _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation D U K i where
  compactSystem := compactSystem
  isCompactPresentation := isCompactPresentation
  ordinarySystem := ordinarySystem
  ordinaryComparison := ordinaryComparison
  stageDuality := stageDuality
  stageFinite := stageFinite

/-- Assemble a morphism of duality presentations from its two system maps and their
ordinary-cohomology and proper-duality compatibility equations. -/
def DualityPresentation.Hom.ofMaps {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    {U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k))}
    {K L : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]}
    {f : K ⟶ L} {i : ℤ} {Pₖ : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation D U K i}
    {Pₗ : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation D U L i}
    (compactMap : Pₗ.compactSystem ⟶ Pₖ.compactSystem)
    (ordinaryMap : Pₖ.ordinarySystem ⟶ Pₗ.ordinarySystem)
    (ordinary_naturality :
      colimMap ordinaryMap ≫ Pₗ.ordinaryComparison.hom =
        Pₖ.ordinaryComparison.hom ≫
          (Cohomology.overFieldFunctor (Over.hom U.obj) i).map f)
    (stage_naturality :
      Pₗ.stageDuality.hom ≫ FiniteDual.diagramMap ordinaryMap =
        Functor.whiskerRight compactMap
            (Cohomology.overFieldFunctor
              (Over.hom (base (Spec (CommRingCat.of k))).obj) (-i)) ≫
          Pₖ.stageDuality.hom) :
    _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom f i Pₖ Pₗ where
  compactMap := compactMap
  ordinaryMap := ordinaryMap
  ordinary_naturality := ordinary_naturality
  stage_naturality := stage_naturality

/-- Identity morphism of a duality presentation. -/
def DualityPresentation.Hom.id {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    {U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k))}
    {K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]}
    {i : ℤ} {P : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation D U K i} :
    _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom (𝟙 K) i P P where
  compactMap := 𝟙 _
  ordinaryMap := 𝟙 _
  ordinary_naturality := sorry
  stage_naturality := sorry

/-- Composition of morphisms of duality presentations. -/
def DualityPresentation.Hom.comp {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    {U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k))}
    {K L M : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]}
    {f : K ⟶ L} {g : L ⟶ M} {i : ℤ}
    {Pₖ : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation D U K i}
    {Pₗ : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation D U L i}
    {Pₘ : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation D U M i}
    (α : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom f i Pₖ Pₗ)
    (β : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom g i Pₗ Pₘ) :
    _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom (f ≫ g) i Pₖ Pₘ where
  compactMap := β.compactMap ≫ α.compactMap
  ordinaryMap := α.ordinaryMap ≫ β.ordinaryMap
  ordinary_naturality := sorry
  stage_naturality := sorry

/-- A coherent compact-support duality construction for the normalized upper-shriek
assignment `D`. It supplies one presentation for every bounded coherent object and the
presentation morphism induced by every map; proof-only functorial laws are stated separately. -/
structure DualityAssignment {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    (D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk) where
  /-- The functorially selected presentation for each source object and degree. -/
  presentation (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    DualityPresentation D U K i
  /-- The presentation morphism canonically induced by a morphism of source objects. -/
  presentationMap (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    {K L : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]}
    (f : K ⟶ L) (i : ℤ) :
    DualityPresentation.Hom f i (presentation U K i) (presentation U L i)

/-- Bundle an explicit family of duality presentations together with its morphism-level
construction. -/
def DualityAssignment.ofPresentations {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (presentation : (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k))) →
      (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) →
      (i : ℤ) → _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation D U K i)
    (presentationMap : (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k))) →
      {K L : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]} →
      (f : K ⟶ L) → (i : ℤ) →
      _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom f i (presentation U K i) (presentation U L i)) :
    _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityAssignment D where
  presentation := presentation
  presentationMap := presentationMap

/-- Compactly supported cohomology of `RHom(K, ωU/k)` in degree `-i`, computed from
the selected functorial compact-support system. -/
noncomputable abbrev dualityCohomology {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A : DualityAssignment D)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    ModuleCat.{u} k :=
  cohomology (Over.hom (base (Spec (CommRingCat.of k))).obj)
    (A.presentation U K i).compactSystem (-i)

/-- Compactly supported cohomology is the limit attached to the selected functorial
compact-support system. -/
theorem dualityCohomology_def {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A : DualityAssignment D)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    dualityCohomology A U K i =
      limit (cohomologyDiagram (Over.hom (base (Spec (CommRingCat.of k))).obj)
        (A.presentation U K i).compactSystem (-i)) := sorry

/-- The inverse-limit topology on compactly supported cohomology. -/
@[implicit_reducible]
noncomputable def dualityCohomologyTopology {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A : DualityAssignment D)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    TopologicalSpace (dualityCohomology A U K i) :=
  cohomologyTopology (Over.hom (base (Spec (CommRingCat.of k))).obj)
    (A.presentation U K i).compactSystem (-i)

/-- The compact-support topology is the limit topology of the selected functorial system. -/
theorem dualityCohomologyTopology_def {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A : DualityAssignment D)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    dualityCohomologyTopology A U K i =
      CategoryTheory.Functor.limitTopology
        (cohomologyDiagram (Over.hom (base (Spec (CommRingCat.of k))).obj)
          (A.presentation U K i).compactSystem (-i)) := sorry

/-- The contravariant map on compactly supported cohomology induced by `f : K ⟶ L`. -/
noncomputable def dualityCohomologyMap {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A : DualityAssignment D)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    {K L : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]}
    (f : K ⟶ L) (i : ℤ) :
    dualityCohomology A U L i →ₗ[k] dualityCohomology A U K i :=
  cohomologyMap (Over.hom (base (Spec (CommRingCat.of k))).obj)
    (A.presentationMap U f i).compactMap (-i)

/-- Compactly supported cohomology maps preserve identity morphisms. -/
theorem dualityCohomologyMap_id {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A : DualityAssignment D)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    dualityCohomologyMap A U (𝟙 K) i = LinearMap.id := sorry

/-- Compactly supported cohomology maps preserve contravariant composition. -/
theorem dualityCohomologyMap_comp {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A : DualityAssignment D)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    {K L M : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]}
    (f : K ⟶ L) (g : L ⟶ M) (i : ℤ) :
    dualityCohomologyMap A U (f ≫ g) i =
      (dualityCohomologyMap A U f i).comp (dualityCohomologyMap A U g i) := sorry

/-- The canonical linear comparison from compactly supported cohomology of
`RHom(K, ωU/k)` to the algebraic dual of ordinary cohomology of `K`. -/
noncomputable def dualityComparisonWith {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    (D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ)
    (P : DualityPresentation D U K i) :
    (limit (cohomologyDiagram
      (Over.hom (base (Spec (CommRingCat.of k))).obj) P.compactSystem (-i)) :
        ModuleCat.{u} k) →ₗ[k]
      Module.Dual k (Cohomology.overField (Over.hom U.obj) K i) :=
  ((P.ordinaryComparison.inv).hom.dualMap).comp
    ((FiniteDual.limitToDualColimit P.ordinarySystem).comp
      (limMap P.stageDuality.hom).hom)

/-- The comparison attached to one presentation is the limit of the finite-stage
proper-duality maps followed
by the dual-of-colimit comparison. -/
theorem dualityComparisonWith_def {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    (D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ)
    (P : DualityPresentation D U K i) :
    dualityComparisonWith D U K i P =
      ((P.ordinaryComparison.inv).hom.dualMap).comp
        ((FiniteDual.limitToDualColimit P.ordinarySystem).comp
          (limMap P.stageDuality.hom).hom) := sorry

/-- The compact-support duality comparison attached to a coherent functorial
presentation assignment. -/
noncomputable def dualityComparison {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A : DualityAssignment D)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    dualityCohomology A U K i →ₗ[k]
      Module.Dual k (Cohomology.overField (Over.hom U.obj) K i) :=
  dualityComparisonWith D U K i (A.presentation U K i)

/-- The assignment-relative duality comparison is assembled from its selected
functorial presentation. -/
theorem dualityComparison_def {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A : DualityAssignment D)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    dualityComparison A U K i =
      dualityComparisonWith D U K i (A.presentation U K i) := sorry

/-- A comparison between two coherent compact-support duality assignments, specified by
compatible presentation morphisms on every source object. -/
structure DualityAssignment.Hom {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A B : DualityAssignment D) where
  /-- The comparison between the selected presentations of each object. -/
  app (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    DualityPresentation.Hom (𝟙 K) i (B.presentation U K i) (A.presentation U K i)

/-- Bundle explicit objectwise presentation comparisons into a comparison of duality
assignments. -/
def DualityAssignment.Hom.ofComponents {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    {A B : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityAssignment D}
    (app : (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k))) →
      (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) →
      (i : ℤ) →
      _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom (𝟙 K) i (B.presentation U K i)
        (A.presentation U K i)) :
    _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityAssignment.Hom A B where
  app := app

/-- Identity comparison of a duality assignment. -/
def DualityAssignment.Hom.id {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    {A : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityAssignment D} :
    _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityAssignment.Hom A A where
  app := fun _U _K _i => _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom.id

/-- Composition of comparisons of duality assignments. -/
def DualityAssignment.Hom.comp {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    {A B C : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityAssignment D}
    (α : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityAssignment.Hom A B) (β : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityAssignment.Hom B C) :
    _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityAssignment.Hom A C where
  app := fun U K i => _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom.comp (β.app U K i) (α.app U K i)

/-- A comparison of duality assignments induces the corresponding linear comparison on
compactly supported cohomology. -/
noncomputable def assignmentComparison {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A B : DualityAssignment D) (C : DualityAssignment.Hom A B)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    dualityCohomology A U K i →ₗ[k] dualityCohomology B U K i :=
  cohomologyMap (Over.hom (base (Spec (CommRingCat.of k))).obj)
    (C.app U K i).compactMap (-i)

/-- The carrier comparison induced by a comparison of duality assignments is bijective. -/
theorem assignmentComparison_bijective {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A B : DualityAssignment D) (C : DualityAssignment.Hom A B)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    Function.Bijective (assignmentComparison A B C U K i) := sorry

/-- A comparison of duality assignments identifies their compact-support topologies. -/
theorem assignmentComparison_topology {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A B : DualityAssignment D) (C : DualityAssignment.Hom A B)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    dualityCohomologyTopology A U K i =
      TopologicalSpace.induced (assignmentComparison A B C U K i)
        (dualityCohomologyTopology B U K i) := sorry

/-- The duality map is compatible with comparison between compact-support assignments. -/
theorem dualityComparison_assignment {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A B : DualityAssignment D) (C : DualityAssignment.Hom A B)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    (dualityComparison B U K i).comp (assignmentComparison A B C U K i) =
      dualityComparison A U K i := sorry

/-- The induced map on compactly supported cohomology is independent of the chosen
comparison between two coherent assignments. -/
theorem assignmentComparison_independent {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {ωk : RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace}
    {hωk : ωk.IsDualizingComplex H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H ωk hωk}
    (A B : DualityAssignment D) (C E : DualityAssignment.Hom A B)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    assignmentComparison A B C U K i = assignmentComparison A B E U K i := sorry

/-- Compactly supported cohomology of `RHom(K, ω_{U/k})` is canonically linearly
isomorphic to the algebraic dual of ordinary cohomology of `K`. -/
theorem dualityComparison_bijective {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {hStructureSheaf : RingedSpace.ModuleDerived.IsDualizingComplex
      (Scheme.DerivedQCoh.structureSheaf (Spec (CommRingCat.of k))).obj H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H
      (Scheme.DerivedQCoh.structureSheaf (Spec (CommRingCat.of k))).obj hStructureSheaf}
    (A : DualityAssignment D)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    Function.Bijective (dualityComparison A U K i) := sorry

/-- The canonical comparison identifies the inverse-limit topology on compactly
supported cohomology with the finite topology on the algebraic dual of ordinary
cohomology. -/
theorem dualityComparison_topology {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {hStructureSheaf : RingedSpace.ModuleDerived.IsDualizingComplex
      (Scheme.DerivedQCoh.structureSheaf (Spec (CommRingCat.of k))).obj H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H
      (Scheme.DerivedQCoh.structureSheaf (Spec (CommRingCat.of k))).obj hStructureSheaf}
    (A : DualityAssignment D)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    (K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]) (i : ℤ) :
    dualityCohomologyTopology A U K i =
      TopologicalSpace.induced (dualityComparison A U K i)
        (FiniteDual.topology k (Cohomology.overField (Over.hom U.obj) K i)) := sorry

/-- The compact-support duality comparison is contravariantly natural for morphisms
of bounded coherent complexes. -/
theorem dualityComparison_naturality {k : Type u} [Field k]
    [MonoidalCategory (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]
    {H : MonoidalClosed
      (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)}
    {hStructureSheaf : RingedSpace.ModuleDerived.IsDualizingComplex
      (Scheme.DerivedQCoh.structureSheaf (Spec (CommRingCat.of k))).obj H}
    {D : NewUpperShriekAssignment (Spec (CommRingCat.of k)) H
      (Scheme.DerivedQCoh.structureSheaf (Spec (CommRingCat.of k))).obj hStructureSheaf}
    (A : DualityAssignment D)
    (U : FiniteTypeSeparatedOver (Spec (CommRingCat.of k)))
    {K L : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]} (f : K ⟶ L)
    (i : ℤ) :
    ((Cohomology.overFieldFunctor (Over.hom U.obj) i).map f).hom.dualMap.comp
        (dualityComparison A U L i) =
      (dualityComparison A U K i).comp (dualityCohomologyMap A U f i) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
