/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Limits
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Finite
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Closure
import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.KProjective

/-!
# Finite-Cell Models of Compact Derived Objects

Finite-cell DG-modules define an object property in the intrinsic derived category through the
essential image of the module-to-derived functor.  This leaf owns finite-support factorization and
the identification of compact objects with the canonical retract closure of that property.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.Derived

open PropertyP

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/-- A map from a compact derived object into a property-P module factors through one filtration
stage.  This is the colimit-facing compactness primitive for finite-support arguments. -/
@[stacks 09R2 "compact factorization through a property-P stage"]
theorem exists_factorization_through_propertyP_stage
    (E : Category.{u, v} A) (hE : IsCompactObject E)
    {P : DifferentialGradedModule.{u, v} A} (F : Filtration A P)
    (f : E ⟶ (fromModules A).obj P) :
    ∃ (n : ℕ) (g : E ⟶ (fromModules A).obj (F.stage n)),
      g ≫ (fromModules A).map (F.coconeApp n) = f := sorry

/-- After mapping an arrow out of a compact object from a finite property-P stage to the ambient
module, it factors through a chosen finite-summand subfiltration. -/
@[stacks 09R2 "stagewise finite-subfiltration factorization"]
theorem exists_finiteSubfiltration_factorization_of_stage
    (E : Category.{u, v} A) (hE : IsCompactObject E)
    {P : DifferentialGradedModule.{u, v} A} (F : Filtration A P) (n : ℕ)
    (f : E ⟶ (fromModules A).obj (F.stage n)) :
    ∃ (F' : FiniteSubfiltration A F)
      (g : E ⟶ (fromModules A).obj F'.obj),
      g ≫ (fromModules A).map F'.subobject.arrow =
        f ≫ (fromModules A).map (F.coconeApp n) := sorry

/-- A map from a compact derived object into a module with a property-P filtration factors
through a DG-submodule retaining finitely many cell summands. -/
@[stacks 09R2 "finite-subfiltration factorization"]
theorem exists_finiteSubfiltration_factorization
    (E : Category.{u, v} A) (hE : IsCompactObject E)
    {P : DifferentialGradedModule.{u, v} A} (F : Filtration A P)
    (f : E ⟶ (fromModules A).obj P) :
    ∃ (F' : FiniteSubfiltration A F)
      (g : E ⟶ (fromModules A).obj F'.obj),
      g ≫ (fromModules A).map F'.subobject.arrow = f := by
  obtain ⟨n, g, hg⟩ := exists_factorization_through_propertyP_stage A E hE F f
  obtain ⟨F', g', hg'⟩ := exists_finiteSubfiltration_factorization_of_stage A E hE F n g
  exact ⟨F', g', hg'.trans hg⟩

/-- Lemma 22.36.3 (09R2): a map from a compact derived object into a DG-module with a chosen
finite property-P filtration factors through a DG-submodule retaining finitely many summands in
each filtration piece. -/
@[stacks 09R2]
theorem exists_factorization_through_finiteSubfiltration
    (E : Category.{u, v} A) (hE : IsCompactObject E)
    {P : DifferentialGradedModule.{u, v} A} (F : FiniteFiltration A P)
    (f : E ⟶ (fromModules A).obj P) :
    ∃ (F' : FiniteSubfiltration A F.toFiltration)
      (g : E ⟶ (fromModules A).obj F'.obj),
      g ≫ (fromModules A).map F'.subobject.arrow = f := by
  exact exists_finiteSubfiltration_factorization A E hE F.toFiltration f

/-- Derived objects represented by DG-modules with finite-cell property-P filtrations. -/
@[stacks 09R3 "finite-cell objects in the derived category"]
def finiteCell : ObjectProperty (Category.{u, v} A) :=
  (HasFiniteCellFiltration A).map (fromModules A)

/-- A derived object is finite-cell exactly when it is represented by a DG-module carrying a
finite-cell property-P filtration. -/
@[stacks 09R3 "finite-cell representation criterion"]
theorem finiteCell_iff (E : Category.{u, v} A) :
    finiteCell A E ↔
      ∃ (P : DifferentialGradedModule.{u, v} A), HasFiniteCellFiltration A P ∧
        Nonempty ((fromModules A).obj P ≅ E) := Iff.rfl

namespace FiniteCell

/-- Finite-cell derived objects are closed under isomorphisms. -/
@[stacks 09R3 "isomorphism stability of finite-cell objects"]
instance isClosedUnderIsomorphisms :
    (finiteCell A).IsClosedUnderIsomorphisms :=
  inferInstanceAs ((HasFiniteCellFiltration A).map (fromModules A)).IsClosedUnderIsomorphisms

/-- A finite-cell derived object is compact. -/
@[stacks 09R3 "finite-cell objects are compact"]
theorem isCompactObject {E : Category.{u, v} A} (hE : finiteCell A E) :
    IsCompactObject E := sorry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem preservesColimit_of_functorRetract
    {C D J : Type*} [CategoryTheory.Category C] [CategoryTheory.Category D]
    [CategoryTheory.Category J] {K : J ⥤ C} {F G : C ⥤ D}
    (r : Retract F G) [PreservesColimit K G] : PreservesColimit K F where
  preserves {c} hc := by
    let hG := isColimitOfPreserves G hc
    let t (s : Cocone (K ⋙ F)) : Cocone (K ⋙ G) :=
      { pt := s.pt, ι := Functor.whiskerLeft K r.r ≫ s.ι }
    have hfac (s : Cocone (K ⋙ F)) (j : J) :
        G.map (c.ι.app j) ≫ hG.desc (t s) = r.r.app (K.obj j) ≫ s.ι.app j := by
      simpa [t] using hG.fac (t s) j
    refine ⟨{ desc := fun s ↦ r.i.app c.pt ≫ hG.desc (t s)
              fac := ?_
              uniq := ?_ }⟩
    · intro s j
      simp only [Functor.mapCocone_ι_app, Functor.comp_obj]
      rw [← Category.assoc, r.i.naturality, Category.assoc, hfac s j]
      rw [← Category.assoc, ← NatTrans.comp_app, r.retract]
      simp
    · intro s m hm
      have hr : r.r.app c.pt ≫ m = hG.desc (t s) := by
        apply hG.hom_ext
        intro j
        simp only [Functor.mapCocone_ι_app, Functor.comp_obj] at hm ⊢
        rw [← Category.assoc, r.r.naturality, Category.assoc, hm j, hfac s j]
      calc
        m = (r.i.app c.pt ≫ r.r.app c.pt) ≫ m := by
          rw [← NatTrans.comp_app, r.retract]
          simp
        _ = r.i.app c.pt ≫ hG.desc (t s) := by
          rw [Category.assoc, hr]

/-- Every object in the retract closure of finite-cell derived objects is compact. -/
@[stacks 09R3 "compactness of the finite-cell retract closure"]
theorem isCompactObject_of_mem_retractClosure {E : Category.{u, v} A}
    (hE : (finiteCell A).retractClosure E) : IsCompactObject E := by
  obtain ⟨P, hP, ⟨r⟩⟩ := hE
  have hcompact := isCompactObject A hP
  refine ⟨fun I ↦ ?_⟩
  letI := hcompact.preservesCoproducts I
  exact ⟨fun {K} ↦ preservesColimit_of_functorRetract (r.op.map preadditiveCoyoneda)⟩

/-- Every compact derived object belongs to the retract closure of finite-cell objects. -/
@[stacks 09R3 "compact objects lie in the finite-cell retract closure"]
theorem mem_retractClosure_of_isCompactObject {E : Category.{u, v} A}
    (hE : IsCompactObject E) : (finiteCell A).retractClosure E := sorry

/-- Proposition 22.36.4 (09R3): compact derived objects are exactly the retract closure of the
finite-cell objects. -/
@[stacks 09R3]
theorem isCompactObject_iff_mem_retractClosure (E : Category.{u, v} A) :
    IsCompactObject E ↔ (finiteCell A).retractClosure E :=
  ⟨mem_retractClosure_of_isCompactObject A, isCompactObject_of_mem_retractClosure A⟩

end FiniteCell

#synth (finiteCell A).IsClosedUnderIsomorphisms

end DifferentialGradedModule.Derived
