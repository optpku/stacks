/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Absolute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Characteristic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import ReasLib.CategoryTheory.Sites.Sheafification.Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.Sheaf

/-!
# Frobenius-colimit sheaf on a chosen big h site

This module constructs the sectionwise Frobenius diagram, its presheaf colimit, and the
associated ring-valued h-sheaf over a represented base of characteristic `p`.

The chosen site and represented schemes are kept in one universe to satisfy the universe
bounds of concrete `RingCat` sheafification.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit

/-- The `p`-power endomorphism of the global-sections ring at a represented object. -/
def frobeniusAt (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p]
    (U : (Over S)ᵒᵖ) :
    (Scheme.Site.structurePresheaf (ChosenBigSite.sliceToScheme Schh S)).obj U ⟶
      (Scheme.Site.structurePresheaf (ChosenBigSite.sliceToScheme Schh S)).obj U :=
  RingCat.ofHom <| RingHom.frobeniusOfPrime p <|
    (Scheme.Hom.isCharP_of_target (p := p)
      (Schh.toScheme.map (unop U).hom)).cast_eq_zero ⊤

/-- The componentwise Frobenius endomorphism sends every section to its `p`-th power. -/
theorem frobeniusAt_apply (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p]
    (U : (Over S)ᵒᵖ)
    (s : (Scheme.Site.structurePresheaf
      (ChosenBigSite.sliceToScheme Schh S)).obj U) :
    RingCat.Hom.hom (frobeniusAt p Schh S U) s = s ^ p := sorry

/-- Frobenius on represented global sections is natural under restriction. -/
theorem map_naturality (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p]
    {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (Scheme.Site.structurePresheaf (ChosenBigSite.sliceToScheme Schh S)).map f ≫
        frobeniusAt p Schh S V =
      frobeniusAt p Schh S U ≫
        (Scheme.Site.structurePresheaf (ChosenBigSite.sliceToScheme Schh S)).map f := sorry

/-- The sectionwise Frobenius natural endomorphism of the represented structure presheaf. -/
def map (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    Scheme.Site.structurePresheaf (ChosenBigSite.sliceToScheme Schh S) ⟶
      Scheme.Site.structurePresheaf (ChosenBigSite.sliceToScheme Schh S) where
  app U := frobeniusAt p Schh S U
  naturality {_ _} f := map_naturality p Schh S f

/-- The Frobenius natural transformation sends every represented section to its
`p`-th power. -/
theorem map_apply (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p]
    (U : (Over S)ᵒᵖ)
    (s : (Scheme.Site.structurePresheaf
      (ChosenBigSite.sliceToScheme Schh S)).obj U) :
    RingCat.Hom.hom ((map p Schh S).app U) s = s ^ p := sorry

/-- The sequential diagram of represented global-sections presheaves under Frobenius. -/
def diagram (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    ℕ ⥤ ((Over S)ᵒᵖ ⥤ RingCat.{u}) :=
  Functor.ofSequence (fun _ : ℕ ↦ map p Schh S)

/-- Every object of the presheaf Frobenius diagram is the represented structure presheaf. -/
theorem diagram_obj (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] (n : ℕ) :
    (diagram p Schh S).obj n =
      Scheme.Site.structurePresheaf (ChosenBigSite.sliceToScheme Schh S) := sorry

/-- Every successor map in the presheaf diagram is sectionwise Frobenius. -/
theorem diagram_map_succ (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] (n : ℕ) :
    (diagram p Schh S).map (homOfLE n.le_succ) = map p Schh S := sorry

/-- The presheaf colimit of represented global sections under sectionwise Frobenius. -/
noncomputable def rawPresheaf (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    (Over S)ᵒᵖ ⥤ RingCat.{u} :=
  colimit (diagram p Schh S)

/-- The presheaf colimit of represented global sections under sectionwise Frobenius
satisfies descent for the chosen big h topology. -/
theorem rawPresheaf_isSheaf (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    Presheaf.IsSheaf (bigTopology Schh S) (rawPresheaf p Schh S) := sorry

/-- The canonical map from a Frobenius stage to the presheaf colimit. -/
noncomputable def rawPresheafStage (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (n : ℕ) :
    Scheme.Site.structurePresheaf (ChosenBigSite.sliceToScheme Schh S) ⟶
      rawPresheaf p Schh S :=
  colimit.ι (diagram p Schh S) n

/-- Successive stage maps to the raw presheaf colimit are compatible with Frobenius. -/
theorem rawPresheafStage_succ (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (n : ℕ) :
    map p Schh S ≫ rawPresheafStage p Schh S (n + 1) =
      rawPresheafStage p Schh S n := sorry

/-- The concrete double-plus construction on the Frobenius-colimit presheaf is a Zariski
sheaf. -/
theorem zariskiSheafification_isSheaf (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    Presheaf.IsSheaf (bigZariskiTopology Schh S)
      ((bigZariskiTopology Schh S).sheafify (rawPresheaf p Schh S)) := sorry

/-- The Zariski sheafification of the sectionwise Frobenius-colimit presheaf. -/
noncomputable def zariskiSheaf (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    Sheaf (bigZariskiTopology Schh S) RingCat.{u} :=
  ⟨(bigZariskiTopology Schh S).sheafify (rawPresheaf p Schh S),
    zariskiSheafification_isSheaf p Schh S⟩

/-- The underlying presheaf of `zariskiSheaf` is the canonical Zariski sheafification. -/
theorem zariskiSheaf_obj (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    (zariskiSheaf p Schh S).obj =
      (bigZariskiTopology Schh S).sheafify (rawPresheaf p Schh S) := sorry

/-- The Zariski-sheafified Frobenius colimit satisfies descent for the chosen big h topology. -/
theorem isSheaf (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    Presheaf.IsSheaf (bigTopology Schh S) (zariskiSheaf p Schh S).obj := sorry

/-- The ring-valued h-sheaf obtained from the sectionwise Frobenius colimit. -/
noncomputable def sheaf (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    Sheaf (bigTopology Schh S) RingCat.{u} :=
  ⟨(zariskiSheaf p Schh S).obj, isSheaf p Schh S⟩

/-- The underlying presheaf of the h-sheaf is the Zariski sheafification of the raw
Frobenius colimit. -/
theorem sheaf_obj (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    (sheaf p Schh S).obj = (zariskiSheaf p Schh S).obj := sorry

/-- The canonical morphism from the raw Frobenius-colimit presheaf to its h-sheaf. -/
noncomputable def toSheaf (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    rawPresheaf p Schh S ⟶ (sheaf p Schh S).obj :=
  (bigZariskiTopology Schh S).toSheafify (rawPresheaf p Schh S)

/-- The Frobenius diagram evaluated at a represented object. -/
def sectionsDiagram (p : ℕ) [Fact p.Prime] (Schh : ChosenBigHSite.{u, u})
    (S : Schh.carrier) [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) :
    ℕ ⥤ RingCat.{u} :=
  diagram p Schh S ⋙ (evaluation (Over S)ᵒᵖ RingCat.{u}).obj (op U)

/-- Every stage of the evaluated diagram is the global-sections ring of the represented
scheme. -/
theorem sectionsDiagram_obj (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) (n : ℕ) :
    (sectionsDiagram p Schh S U).obj n =
      (Scheme.Site.structurePresheaf
        (ChosenBigSite.sliceToScheme Schh S)).obj (op U) := sorry

/-- Every successor map in the evaluated diagram is Frobenius on global sections. -/
theorem sectionsDiagram_map_succ (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) (n : ℕ) :
    (sectionsDiagram p Schh S U).map (homOfLE n.le_succ) =
      (map p Schh S).app (op U) := sorry

/-- The evaluated stage maps form a cocone with vertex the value of the h-sheaf. -/
theorem sectionsCocone_naturality (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S)
    {i j : ℕ} (f : i ⟶ j) :
    (sectionsDiagram p Schh S U).map f ≫
        (rawPresheafStage p Schh S j).app (op U) ≫
          (toSheaf p Schh S).app (op U) =
      (rawPresheafStage p Schh S i).app (op U) ≫
          (toSheaf p Schh S).app (op U) ≫
        ((Functor.const ℕ).obj ((sheaf p Schh S).obj.obj (op U))).map f := sorry

/-- The canonical cocone from the evaluated Frobenius diagram to the h-sheaf value. -/
noncomputable def sectionsCocone (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) :
    Cocone (sectionsDiagram p Schh S U) where
  pt := (sheaf p Schh S).obj.obj (op U)
  ι :=
    { app := fun n ↦
        (rawPresheafStage p Schh S n).app (op U) ≫
          (toSheaf p Schh S).app (op U)
      naturality := fun {_ _} f ↦ sectionsCocone_naturality p Schh S U f }

/-- The leg of the canonical evaluated cocone is the corresponding raw stage map followed
by the sheafification map. -/
theorem sectionsCocone_ι (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) (n : ℕ) :
    (sectionsCocone p Schh S U).ι.app n =
      (rawPresheafStage p Schh S n).app (op U) ≫
        (toSheaf p Schh S).app (op U) := sorry

/-- The canonical comparison from the colimit of global sections under Frobenius to the
value of the h-sheaf. -/
noncomputable def sectionsToSheaf (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) :
    colimit (sectionsDiagram p Schh S U) ⟶ (sheaf p Schh S).obj.obj (op U) :=
  colimit.desc (sectionsDiagram p Schh S U) (sectionsCocone p Schh S U)

/-- The value comparison agrees with the canonical map from every Frobenius stage. -/
theorem sectionsToSheaf_fac (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S) (n : ℕ) :
    colimit.ι (sectionsDiagram p Schh S U) n ≫ sectionsToSheaf p Schh S U =
      (rawPresheafStage p Schh S n).app (op U) ≫
        (toSheaf p Schh S).app (op U) := sorry

/-- The canonical map from the sectionwise Frobenius colimit to the associated h-sheaf
exhibits the latter as a sheafification for the chosen big h topology. -/
theorem toSheaf_isSheafification (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] :
    Presheaf.IsSheafification (bigTopology Schh S) (toSheaf p Schh S) := sorry

/-- On a quasi-compact and quasi-separated represented object, the canonical map from the
Frobenius colimit of global sections to the associated h-sheaf value is an isomorphism. -/
@[instance]
theorem instIsIsoSectionsToSheaf (p : ℕ) [Fact p.Prime]
    (Schh : ChosenBigHSite.{u, u}) (S : Schh.carrier)
    [Scheme.IsCharP (Schh.toScheme.obj S) p] (U : Over S)
    [CompactSpace ((ChosenBigSite.sliceToScheme Schh S).obj U)]
    [QuasiSeparatedSpace ((ChosenBigSite.sliceToScheme Schh S).obj U)] :
    IsIso (sectionsToSheaf p Schh S U) := sorry

end AlgebraicGeometry.ChosenBigHSite.FrobeniusColimit
