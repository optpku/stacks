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
  /-- A morphism may move to later finite stages (e.g. multiplication by a coordinate). -/
  reindex : ℕ+ →o ℕ+
  /-- The reindexing is cofinal: every stage is bounded by its image. -/
  le_reindex : ∀ n, n ≤ reindex n
  /-- The compact map runs from the reindexed target tower to the source tower. -/
  compactMap : reindex.dual.monotone.functor ⋙ Pₗ.compactSystem ⟶ Pₖ.compactSystem
  /-- The ordinary map may increase the finite-stage index. -/
  ordinaryMap : Pₖ.ordinarySystem ⟶ reindex.monotone.functor ⋙ Pₗ.ordinarySystem
  /-- Each stage map induces the actual coefficient map on ordinary cohomology. -/
  ordinary_naturality : ∀ n,
    ordinaryMap.app n ≫ colimit.ι Pₗ.ordinarySystem (reindex n) ≫
        Pₗ.ordinaryComparison.hom =
      colimit.ι Pₖ.ordinarySystem n ≫ Pₖ.ordinaryComparison.hom ≫
        (Cohomology.overFieldFunctor (Over.hom U.obj) i).map f
  /-- Proper duality commutes with the two maps at their respective indices. -/
  stage_naturality : ∀ n : ℕ+,
    Pₗ.stageDuality.hom.app (OrderDual.toDual (reindex n)) ≫
        ModuleCat.ofHom (ordinaryMap.app n).hom.dualMap =
      (Cohomology.overFieldFunctor
          (Over.hom (base (Spec (CommRingCat.of k))).obj) (-i)).map
          (compactMap.app (OrderDual.toDual n)) ≫
        Pₖ.stageDuality.hom.app (OrderDual.toDual n)

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
    (reindex : ℕ+ →o ℕ+) (le_reindex : ∀ n, n ≤ reindex n)
    (compactMap : reindex.dual.monotone.functor ⋙ Pₗ.compactSystem ⟶ Pₖ.compactSystem)
    (ordinaryMap : Pₖ.ordinarySystem ⟶ reindex.monotone.functor ⋙ Pₗ.ordinarySystem)
    (ordinary_naturality : ∀ n,
      ordinaryMap.app n ≫ colimit.ι Pₗ.ordinarySystem (reindex n) ≫
          Pₗ.ordinaryComparison.hom =
        colimit.ι Pₖ.ordinarySystem n ≫ Pₖ.ordinaryComparison.hom ≫
          (Cohomology.overFieldFunctor (Over.hom U.obj) i).map f)
    (stage_naturality : ∀ n : ℕ+,
      Pₗ.stageDuality.hom.app (OrderDual.toDual (reindex n)) ≫
          ModuleCat.ofHom (ordinaryMap.app n).hom.dualMap =
        (Cohomology.overFieldFunctor
            (Over.hom (base (Spec (CommRingCat.of k))).obj) (-i)).map
            (compactMap.app (OrderDual.toDual n)) ≫
          Pₖ.stageDuality.hom.app (OrderDual.toDual n)) :
    _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom f i Pₖ Pₗ where
  reindex := reindex
  le_reindex := le_reindex
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
  reindex := OrderHom.id
  le_reindex := fun _ => le_rfl
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
  reindex := β.reindex.comp α.reindex
  le_reindex := fun n => (α.le_reindex n).trans (β.le_reindex (α.reindex n))
  compactMap := Functor.whiskerLeft α.reindex.dual.monotone.functor β.compactMap ≫
    α.compactMap
  ordinaryMap := α.ordinaryMap ≫
    Functor.whiskerLeft α.reindex.monotone.functor β.ordinaryMap
  ordinary_naturality := sorry
  stage_naturality := sorry

/-- Realize a reindexed presentation morphism on compact cohomology by restricting
limit coordinates along its index map and then applying its compact-system map. -/
noncomputable def DualityPresentation.Hom.cohomologyMap {k : Type u} [Field k]
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
    (α : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom f i Pₖ Pₗ) :
    cohomology (Over.hom (base (Spec (CommRingCat.of k))).obj) Pₗ.compactSystem (-i) →ₗ[k]
      cohomology (Over.hom (base (Spec (CommRingCat.of k))).obj) Pₖ.compactSystem (-i) :=
  (limit.pre (cohomologyDiagram
      (Over.hom (base (Spec (CommRingCat.of k))).obj) Pₗ.compactSystem (-i))
      α.reindex.dual.monotone.functor ≫
    limMap (Functor.whiskerRight α.compactMap
      (Cohomology.overFieldFunctor
        (Over.hom (base (Spec (CommRingCat.of k))).obj) (-i)))).hom

/-- Descend a reindexed ordinary-system map to its colimit. -/
noncomputable def DualityPresentation.Hom.ordinaryCohomologyMap {k : Type u} [Field k]
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
    (α : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom f i Pₖ Pₗ) :
    colimit Pₖ.ordinarySystem ⟶ colimit Pₗ.ordinarySystem :=
  colimMap α.ordinaryMap ≫ colimit.pre Pₗ.ordinarySystem α.reindex.monotone.functor

/-- The map on ordinary colimits is the actual coefficient map under the presentation
comparisons. -/
theorem DualityPresentation.Hom.ordinaryCohomologyMap_naturality {k : Type u} [Field k]
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
    (α : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom f i Pₖ Pₗ) :
    α.ordinaryCohomologyMap ≫ Pₗ.ordinaryComparison.hom =
      Pₖ.ordinaryComparison.hom ≫
        (Cohomology.overFieldFunctor (Over.hom U.obj) i).map f := by
  apply colimit.hom_ext
  intro n
  simpa [DualityPresentation.Hom.ordinaryCohomologyMap, Category.assoc]
    using α.ordinary_naturality n

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
  (A.presentationMap U f i).cohomologyMap

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

section ReindexedNaturality

variable {k : Type u} [Field k]
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

/-- Evaluation of the duality comparison on an ordinary stage is the proper-duality
pairing at that stage. -/
theorem dualityComparisonWith_stage
    {K : Dᵇ[SheafOfModules.isCoherent (Over.left U.obj).ringCatSheaf]}
    (P : DualityPresentation D U K i)
    (x : cohomology (Over.hom (base (Spec (CommRingCat.of k))).obj)
      P.compactSystem (-i)) (n : ℕ+) (v : P.ordinarySystem.obj n) :
    dualityComparisonWith D U K i P x
        ((colimit.ι P.ordinarySystem n ≫ P.ordinaryComparison.hom).hom v) =
      (show Module.Dual k (P.ordinarySystem.obj n) from
        (P.stageDuality.hom.app (OrderDual.toDual n)).hom
          ((limit.π (cohomologyDiagram
            (Over.hom (base (Spec (CommRingCat.of k))).obj)
            P.compactSystem (-i)) (OrderDual.toDual n)).hom x)) v := by
  let C := cohomologyDiagram (Over.hom (base (Spec (CommRingCat.of k))).obj)
    P.compactSystem (-i)
  have hi : P.ordinaryComparison.inv.hom
      (P.ordinaryComparison.hom.hom ((colimit.ι P.ordinarySystem n).hom v)) =
        (colimit.ι P.ordinarySystem n).hom v := by
    change ((P.ordinaryComparison.hom ≫ P.ordinaryComparison.inv).hom)
      ((colimit.ι P.ordinarySystem n).hom v) = _
    rw [P.ordinaryComparison.hom_inv_id]
    rfl
  change FiniteDual.limitToDualColimit P.ordinarySystem
      ((limMap P.stageDuality.hom).hom x)
      (P.ordinaryComparison.inv.hom
        (P.ordinaryComparison.hom.hom ((colimit.ι P.ordinarySystem n).hom v))) = _
  rw [hi]
  have he := congrArg (fun m => m ((limMap P.stageDuality.hom).hom x) v)
    (FiniteDual.limitToDualColimit_comp_ι P.ordinarySystem n)
  have hp := congrArg
    (fun m : limit C ⟶ (FiniteDual.diagram P.ordinarySystem).obj (OrderDual.toDual n) =>
      (show Module.Dual k (P.ordinarySystem.obj n) from m.hom x) v)
    (limMap_π P.stageDuality.hom (OrderDual.toDual n))
  exact he.trans hp

set_option backward.isDefEq.respectTransparency false in
/-- Reindexed morphisms of presentations induce the dual of the actual coefficient map
on the final ordinary/compact cohomology pairings. -/
theorem DualityPresentation.Hom.duality_naturality
    (α : _root_.AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport.DualityPresentation.Hom f i Pₖ Pₗ) :
    ((Cohomology.overFieldFunctor (Over.hom U.obj) i).map f).hom.dualMap.comp
        (dualityComparisonWith D U L i Pₗ) =
      (dualityComparisonWith D U K i Pₖ).comp α.cohomologyMap := by
  ext x y
  let a := ((Cohomology.overFieldFunctor (Over.hom U.obj) i).map f).hom.dualMap
    (dualityComparisonWith D U L i Pₗ x)
  let b := dualityComparisonWith D U K i Pₖ (α.cohomologyMap x)
  have hab : ModuleCat.ofHom (a.comp Pₖ.ordinaryComparison.hom.hom) =
      ModuleCat.ofHom (b.comp Pₖ.ordinaryComparison.hom.hom) := by
    apply colimit.hom_ext
    intro n
    apply ModuleCat.hom_ext
    ext v
    have ho := congrArg (fun m => m.hom v) (α.ordinary_naturality n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at ho
    change dualityComparisonWith D U L i Pₗ x
        (((Cohomology.overFieldFunctor (Over.hom U.obj) i).map f).hom
          (Pₖ.ordinaryComparison.hom.hom ((colimit.ι Pₖ.ordinarySystem n).hom v))) =
      dualityComparisonWith D U K i Pₖ (α.cohomologyMap x)
        ((colimit.ι Pₖ.ordinarySystem n ≫ Pₖ.ordinaryComparison.hom).hom v)
    rw [← ho]
    change dualityComparisonWith D U L i Pₗ x
        ((colimit.ι Pₗ.ordinarySystem (α.reindex n) ≫ Pₗ.ordinaryComparison.hom).hom
          ((α.ordinaryMap.app n).hom v)) = _
    rw [dualityComparisonWith_stage, dualityComparisonWith_stage]
    have hc :
        (limit.π (cohomologyDiagram
          (Over.hom (base (Spec (CommRingCat.of k))).obj) Pₖ.compactSystem (-i))
          (OrderDual.toDual n)).hom (α.cohomologyMap x) =
        ((Cohomology.overFieldFunctor
          (Over.hom (base (Spec (CommRingCat.of k))).obj) (-i)).map
          (α.compactMap.app (OrderDual.toDual n))).hom
          ((limit.π (cohomologyDiagram
            (Over.hom (base (Spec (CommRingCat.of k))).obj) Pₗ.compactSystem (-i))
            (OrderDual.toDual (α.reindex n))).hom x) := by
      change ((limit.pre (cohomologyDiagram
          (Over.hom (base (Spec (CommRingCat.of k))).obj) Pₗ.compactSystem (-i))
          α.reindex.dual.monotone.functor ≫
        limMap (Functor.whiskerRight α.compactMap
          (Cohomology.overFieldFunctor
            (Over.hom (base (Spec (CommRingCat.of k))).obj) (-i))) ≫
        limit.π (cohomologyDiagram
          (Over.hom (base (Spec (CommRingCat.of k))).obj) Pₖ.compactSystem (-i))
          (OrderDual.toDual n)).hom) x = _
      simp only [cohomologyDiagram, Category.assoc, limMap_π, limit.pre_π_assoc]
      rfl
    rw [hc]
    exact congrArg (fun m =>
      (show Module.Dual k (Pₖ.ordinarySystem.obj n) from m.hom
        ((limit.π (cohomologyDiagram
          (Over.hom (base (Spec (CommRingCat.of k))).obj) Pₗ.compactSystem (-i))
          (OrderDual.toDual (α.reindex n))).hom x)) v) (α.stage_naturality n)
  have hy : Pₖ.ordinaryComparison.hom.hom (Pₖ.ordinaryComparison.inv.hom y) = y := by
    change ((Pₖ.ordinaryComparison.inv ≫ Pₖ.ordinaryComparison.hom).hom) y = y
    rw [Pₖ.ordinaryComparison.inv_hom_id]
    rfl
  have h := congrArg (fun m => m.hom (Pₖ.ordinaryComparison.inv.hom y)) hab
  simpa only [ModuleCat.hom_ofHom, LinearMap.comp_apply, hy] using h

end ReindexedNaturality

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
  (C.app U K i).cohomologyMap

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
      (dualityComparison A U K i).comp (dualityCohomologyMap A U f i) := by
  exact (A.presentationMap U f i).duality_naturality

end AlgebraicGeometry.Scheme.ModuleDerived.CompactSupport
