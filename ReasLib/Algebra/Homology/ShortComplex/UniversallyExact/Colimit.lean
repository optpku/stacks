/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Tensor

/-!
# Colimits of universally exact module complexes

@stack 058J

This leaf contains the closure properties of universal exactness needed by
lifting and filtered-colimit criteria.  The criteria themselves live in the
neighboring `Criteria` leaf.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe u

namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R]

namespace Splitting

/-- A split short complex of modules is universally exact. -/
theorem universallyExact {S : ShortComplex (ModuleCat.{u} R)}
    (s : S.Splitting) : S.UniversallyExact := by
  refine ⟨s.shortExact, ?_⟩
  intro Q _ _
  have hfr : s.r.hom.comp S.f.hom = LinearMap.id := by
    exact congrArg ModuleCat.Hom.hom s.f_r
  apply LinearMap.injective_of_comp_eq_id (S.f.hom.rTensor Q) (s.r.hom.rTensor Q)
  rw [← LinearMap.rTensor_comp, hfr, LinearMap.rTensor_id]

end Splitting

variable {J : Type u} [Category.{u} J] [IsFiltered J]

namespace ShortExact

/-- A filtered colimit of short exact complexes of modules is short exact. -/
theorem colimit_of_isFiltered
    (F : J ⥤ ShortComplex (ModuleCat.{u} R))
    (hF : ∀ j, (F.obj j).ShortExact) :
    (colimit F).ShortExact := by
  let T : ShortComplex (J ⥤ ModuleCat.{u} R) :=
    (ShortComplex.functorEquivalence J (ModuleCat.{u} R)).inverse.obj F
  have hEval : JointlyFaithful
      ((evaluation J (ModuleCat.{u} R)).obj : J → (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R) := by
    constructor
    intro X Y f g h
    apply NatTrans.ext
    funext j
    exact h j
  have hT : T.ShortExact := by
    rw [hEval.jointlyReflectsIsomorphisms.shortExact_iff]
    intro j
    exact ShortComplex.shortExact_of_iso
      (((ShortComplex.FunctorEquivalence.counitIso J (ModuleCat.{u} R)).app F).app j).symm
      (hF j)
  have hcolimT :
      (T.map (colim : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R)).ShortExact :=
    hT.map_of_exact _
  have hc : (ShortComplex.colimitCocone F).pt.ShortExact := by
    change (ShortComplex.colimitCocone F).pt.ShortExact at hcolimT
    exact hcolimT
  let c : ColimitCocone F :=
    { cocone := ShortComplex.colimitCocone F
      isColimit := ShortComplex.isColimitColimitCocone F }
  exact ShortComplex.shortExact_of_iso (colimit.isoColimitCocone c).symm hc

end ShortExact

private noncomputable instance mapShortComplex_preservesColimit
    (F : J ⥤ ShortComplex (ModuleCat.{u} R))
    (G : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [G.PreservesZeroMorphisms]
    [PreservesColimit (F ⋙ ShortComplex.π₁) G]
    [PreservesColimit (F ⋙ ShortComplex.π₂) G]
    [PreservesColimit (F ⋙ ShortComplex.π₃) G] :
    PreservesColimit F G.mapShortComplex :=
  preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone F)
    (ShortComplex.isColimitOfIsColimitπ _
      (isColimitOfPreserves G (ShortComplex.isColimitπ₁MapCoconeColimitCocone F))
      (isColimitOfPreserves G (ShortComplex.isColimitπ₂MapCoconeColimitCocone F))
      (isColimitOfPreserves G (ShortComplex.isColimitπ₃MapCoconeColimitCocone F)))

namespace UniversallyExact

/-- A filtered colimit of universally exact short complexes is universally
exact. -/
@[stacks 058J]
theorem colimit_of_isFiltered
    (F : J ⥤ ShortComplex (ModuleCat.{u} R))
    (hF : ∀ j, (F.obj j).UniversallyExact) :
    (colimit F).UniversallyExact := by
  refine ⟨ShortExact.colimit_of_isFiltered F (fun j ↦ (hF j).shortExact), ?_⟩
  intro Q _ _
  let Qc : ModuleCat.{u} R := ModuleCat.of R Q
  let G : J ⥤ ShortComplex (ModuleCat.{u} R) :=
    F ⋙ (MonoidalCategory.tensorLeft Qc).mapShortComplex
  have hG : (colimit G).ShortExact :=
    ShortExact.colimit_of_isFiltered G (fun j ↦ tensorLeft_shortExact (hF j) Qc)
  let e : (colimit F).map (MonoidalCategory.tensorLeft Qc) ≅ colimit G :=
    preservesColimitIso (MonoidalCategory.tensorLeft Qc).mapShortComplex F
  have hMap : ((colimit F).map (MonoidalCategory.tensorLeft Qc)).ShortExact :=
    ShortComplex.shortExact_of_iso e.symm hG
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  change Function.Injective
    (((colimit F).map (MonoidalCategory.tensorLeft Qc)).f.hom)
  exact hMap.moduleCat_injective_f

/-- A filtered colimit of split short complexes is universally exact. -/
theorem colimit_of_split
    (F : J ⥤ ShortComplex (ModuleCat.{u} R))
    (hF : ∀ j, Nonempty ((F.obj j).Splitting)) :
    (colimit F).UniversallyExact := by
  apply colimit_of_isFiltered F
  intro j
  obtain ⟨s⟩ := hF j
  exact s.universallyExact

end UniversallyExact

end CategoryTheory.ShortComplex
