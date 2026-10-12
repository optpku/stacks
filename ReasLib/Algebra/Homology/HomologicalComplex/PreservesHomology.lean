/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.CanonicalRows
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functors preserving homology of a homological complex

@stack 015F

Splittings of the canonical cycles--term--image and image--cycles--homology rows give a
fine-grained criterion for an additive functor to preserve homology at one degree.  Injectivity
of the cycles and incoming differential image supplies these splittings.  The resulting
comparison isomorphism is exposed directly at the level of homological complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v₁ v₂ u₁ u₂ w

namespace HomologicalComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable {ι : Type w} {c : ComplexShape ι}

set_option backward.isDefEq.respectTransparency false in
/-- An additive functor preserving finite limits preserves homology at the middle degree when
the canonical cycles--term--image and image--cycles--homology rows both split. -/
theorem preservesLeftHomologyOf_sc_of_splittings
    (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] (i j : ι)
    (hij : c.Rel i j)
    (hCyclesTermImage : (K.cyclesTermImage i j).Splitting)
    (hImageCyclesHomology : (K.imageCyclesHomology i j).Splitting) :
  F.PreservesLeftHomologyOf (K.sc j) := by
  obtain rfl := c.prev_eq' hij
  let h := ShortComplex.LeftHomologyData.canonical (K.sc j)
  let source : CokernelCofork (K.toCycles (c.prev j) j) :=
    CokernelCofork.ofπ (K.homologyπ j) (K.toCycles_comp_homologyπ (c.prev j) j)
  have sourceIsColimit : IsColimit source := K.homologyIsCokernel (c.prev j) j rfl
  have hEpi : Epi (F.map (factorThruImage (K.d (c.prev j) j))) := by
    change Epi ((K.cyclesTermImage (c.prev j) j).map F).g
    exact (hCyclesTermImage.map F).epi_g
  let mappedSource : IsColimit (source.map F) := by
    let base : IsColimit (CokernelCofork.ofπ
        (f := F.map (K.imageToCycles (c.prev j) j))
        (F.map (K.homologyπ j)) (by
          simpa only [F.map_comp, F.map_zero] using
            F.congr_map (K.imageToCycles_homologyπ (c.prev j) j))) := by
      simpa only [ShortComplex.map, imageCyclesHomology_f,
        imageCyclesHomology_g] using (hImageCyclesHomology.map F).gIsCokernel
    have hcomp : F.map (K.toCycles (c.prev j) j) =
        F.map (factorThruImage (K.d (c.prev j) j)) ≫
          F.map (K.imageToCycles (c.prev j) j) := by
      rw [← F.map_comp, K.factorThruImage_imageToCycles (c.prev j) j]
    simpa only [source, CokernelCofork.map, Cofork.π_ofπ] using
      isCokernelEpiComp (hg := hEpi) base
        (F.map (factorThruImage (K.d (c.prev j) j))) hcomp
  have preservesToCycles :
      PreservesColimit (parallelPair (K.toCycles (c.prev j) j) 0) F :=
    preservesColimit_of_preserves_colimit_cocone sourceIsColimit
      (source.isColimitMapCoconeEquiv F |>.symm mappedSource)
  -- Local instance justification (proof-local temporary data): install the preservation witness just constructed.
  letI : h.IsPreservedBy F :=
    { g := by infer_instance
      f' := by
        change PreservesColimit (parallelPair (K.toCycles (c.prev j) j) 0) F
        exact preservesToCycles }
  exact Functor.PreservesLeftHomologyOf.mk' F h

/-- An additive functor preserving finite limits preserves homology at a degree whose cycles
and incoming differential image are injective. -/
theorem preservesLeftHomologyOf_sc_of_injective_cycles_image
    (K : HomologicalComplex C c) (F : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] (i j : ι)
    (hij : c.Rel i j)
    [Injective (K.cycles i)] [Injective (image (K.d i j))] :
    F.PreservesLeftHomologyOf (K.sc j) := by
  -- Local instance justification (proof-local temporary data): transfer the assumed injectivity to this row.
  letI : Injective (K.cyclesTermImage i j).X₁ := by
    change Injective (K.cycles i)
    infer_instance
  -- Local instance justification (proof-local temporary data): transfer the assumed injectivity to this row.
  letI : Injective (K.imageCyclesHomology i j).X₁ := by
    change Injective (image (K.d i j))
    infer_instance
  exact preservesLeftHomologyOf_sc_of_splittings K F i j hij
    ((K.cyclesTermImage_shortExact i j hij).splittingOfInjective)
    ((K.imageCyclesHomology_shortExact i j hij).splittingOfInjective)

/-- The canonical comparison between homology after applying a homology-preserving functor and
the image of the original homology object. -/
noncomputable def mapHomologyIso
    (K : HomologicalComplex C c) (F : C ⥤ D) [F.Additive] (i : ι)
    [F.PreservesLeftHomologyOf (K.sc i)] :
    ((F.mapHomologicalComplex c).obj K).homology i ≅ F.obj (K.homology i) :=
  (K.sc i).mapHomologyIso F

/-- The homological-complex comparison isomorphism is natural in morphisms of complexes. -/
@[reassoc]
theorem mapHomologyIso_hom_naturality
    {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (F : C ⥤ D) [F.Additive] (i : ι)
    [F.PreservesLeftHomologyOf (K.sc i)] [F.PreservesLeftHomologyOf (L.sc i)] :
    homologyMap ((F.mapHomologicalComplex c).map φ) i ≫ (L.mapHomologyIso F i).hom =
      (K.mapHomologyIso F i).hom ≫ F.map (homologyMap φ i) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor C c i).map φ) F

/-- A homology-preserving functor commutes naturally with homology in a
fixed degree on homological complexes. -/
@[stacks 015F "homological-complex homology comparison"]
noncomputable def mapHomologyFunctorIso
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (i : ι) :
    F.mapHomologicalComplex c ⋙ homologyFunctor D c i ≅
      homologyFunctor C c i ⋙ F :=
  NatIso.ofComponents (fun K ↦ K.mapHomologyIso F i)
    (fun φ ↦ mapHomologyIso_hom_naturality φ F i)

namespace mapHomologyFunctorIso

/-- The component of the homological-complex homology comparison is the
canonical objectwise comparison. -/
@[simp]
theorem app (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (K : HomologicalComplex C c) (i : ι) :
    (mapHomologyFunctorIso F i).app K = K.mapHomologyIso F i := rfl

end mapHomologyFunctorIso

end HomologicalComplex
