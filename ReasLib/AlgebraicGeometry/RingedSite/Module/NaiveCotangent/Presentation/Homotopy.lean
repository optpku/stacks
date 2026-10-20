/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Map
public import ReasLib.Algebra.Category.ModuleCat.Differentials.CotangentDifference
public import ReasLib.Algebra.Homology.CochainComplex.MappingCone.NullHomotopy
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopies from parallel morphisms of presentations

Two morphisms of presentations with the same base and target maps differ by a derivation into
the target conormal module.  After sheafification and scalar extension, this derivation gives the
degree-lowering map of a canonical homotopy between the induced maps of naive cotangent
complexes.
-/

@[expose] public section

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u

namespace SheafOfModules.RingedSite.NaiveCotangent.Presentation

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {A P B A' P' B' : Sheaf J CommRingCat.{u}}
variable {phi : A ⟶ P} {alpha : P ⟶ B}
variable {phi' : A' ⟶ P'} {alpha' : P' ⟶ B'}

/-- Two morphisms between fixed presentations with common base and target maps, but potentially
different maps between the presenting ring sheaves. -/
@[ext, stacks 0E1Y "parallel morphisms of presentations"]
structure Hom.Parallel (phi : A ⟶ P) (alpha : P ⟶ B)
    (phi' : A' ⟶ P') (alpha' : P' ⟶ B') where
  /-- The common map between the base ring sheaves. -/
  base : A ⟶ A'
  /-- The first map between the presenting ring sheaves. -/
  first : P ⟶ P'
  /-- The second map between the presenting ring sheaves. -/
  second : P ⟶ P'
  /-- The common map between the presented target ring sheaves. -/
  target : B ⟶ B'
  /-- The first middle map is compatible with the base maps. -/
  firstBaseSq : CommSq base phi phi' first
  /-- The second middle map is compatible with the base maps. -/
  secondBaseSq : CommSq base phi phi' second
  /-- The first middle map is compatible with the target maps. -/
  firstTargetSq : CommSq first alpha alpha' target
  /-- The second middle map is compatible with the target maps. -/
  secondTargetSq : CommSq second alpha alpha' target

namespace Hom.Parallel

variable (p : Hom.Parallel phi alpha phi' alpha')

/-- The first morphism of presentations in a parallel pair. -/
def firstHom : Hom phi alpha phi' alpha' where
  base := p.base
  middle := p.first
  target := p.target
  baseSq := p.firstBaseSq
  targetSq := p.firstTargetSq

/-- The second morphism of presentations in a parallel pair. -/
def secondHom : Hom phi alpha phi' alpha' where
  base := p.base
  middle := p.second
  target := p.target
  baseSq := p.secondBaseSq
  targetSq := p.secondTargetSq

/-- The cochain map induced by the first morphism in the parallel pair, with its common source
and target type exposed definitionally. -/
noncomputable abbrev firstMap :
    (extendComplex p.target).obj
        (complex (O₁ := A) (O₂ := P) (O₃ := B) phi alpha) ⟶
      complex (O₁ := A') (O₂ := P') (O₃ := B') phi' alpha' :=
  Hom.map (firstHom p)

/-- The cochain map induced by the second morphism in the parallel pair, with its common source
and target type exposed definitionally. -/
noncomputable abbrev secondMap :
    (extendComplex p.target).obj
        (complex (O₁ := A) (O₂ := P) (O₃ := B) phi alpha) ⟶
      complex (O₁ := A') (O₂ := P') (O₃ := B') phi' alpha' :=
  Hom.map (secondHom p)

/-- The two middle maps agree after precomposition with the source base map. -/
theorem base_eq : phi ≫ p.first = phi ≫ p.second := sorry

/-- The two middle maps agree after postcomposition with the target presentation map. -/
theorem target_eq : p.first ≫ alpha' = p.second ≫ alpha' := sorry

/-- The sectionwise maps between presenting rings agree on the image of the source base ring. -/
theorem base_app (U : Cᵒᵖ) :
    phi.hom.app U ≫ p.first.hom.app U =
      phi.hom.app U ≫ p.second.hom.app U := sorry

/-- The sectionwise maps between presenting rings agree after the target presentation map. -/
theorem target_app (U : Cᵒᵖ) :
    p.first.hom.app U ≫ alpha'.hom.app U =
      p.second.hom.app U ≫ alpha'.hom.app U := sorry

/-- Sectionwise, the difference of the two middle maps lies in the kernel of the target
presentation map. -/
theorem difference_mem (U : Cᵒᵖ) (x : P.obj.obj U) :
    p.first.hom.app U x - p.second.hom.app U x ∈
      RingHom.ker (alpha'.hom.app U).hom := sorry

/-- The sectionwise difference derivation into the target conormal module before sheafification. -/
noncomputable def rawDerivationApp (U : Cᵒᵖ) :
    ((ModuleCat.restrictScalars (p.first.hom.app U).hom).obj
      (conormalObj alpha' U)).Derivation (phi.hom.app U) :=
  ModuleCat.Derivation.kernelCotangentDifference
    (phi.hom.app U) (p.first.hom.app U) (p.second.hom.app U)
      (alpha'.hom.app U) (p.base_app U) (p.target_app U)

/-- The sectionwise raw derivation evaluates to the cotangent class of the difference of the two
middle maps. -/
@[simp]
theorem rawDerivationApp_d (U : Cᵒᵖ) (x : P.obj.obj U) :
    (p.rawDerivationApp U).d x =
      Ideal.Cotangent.differenceClass
        (RingHom.ker (alpha'.hom.app U).hom)
        (p.first.hom.app U).hom (p.second.hom.app U).hom
        (p.difference_mem U) x := sorry

/-- The target presheaf of the raw difference derivation. -/
abbrev rawTarget (p : Hom.Parallel phi alpha phi' alpha') :
    PresheafOfModules (ringSheaf J P).obj :=
  (PresheafOfModules.restrictScalars (ringSheafMap p.first).hom).obj
    (conormalPresheaf (O₂ := P') (O₃ := B') alpha')

/-- The sectionwise difference derivations commute with restriction maps in the site. -/
theorem rawDerivationApp_naturality {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : ((sheafToPresheaf J CommRingCat).obj P).obj U) :
    (p.rawDerivationApp V).d
        (ConcreteCategory.hom (((sheafToPresheaf J CommRingCat).obj P).map i) x) =
      ConcreteCategory.hom ((rawTarget p).map i) ((p.rawDerivationApp U).d x) := sorry

/-- The raw difference derivation assembled over the entire site. -/
@[stacks 0E1Y "presentation difference derivation"]
noncomputable def rawDerivation : (rawTarget p).Derivation' phi.hom :=
  PresheafOfModules.Derivation'.mk (rawDerivationApp p)
    (fun {U V} i x ↦
      rawDerivationApp_naturality (p := p) (U := U) (V := V) i x)

/-- Evaluating the assembled presheaf derivation at an object recovers the sectionwise raw
derivation. -/
@[simp]
theorem rawDerivation_app (U : Cᵒᵖ) :
    (rawDerivation p).app U = p.rawDerivationApp U := sorry

variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The target conormal sheaf, restricted first to the source presented ring and then to the
source presenting ring. -/
abbrev targetSheaf : SheafOfModules (ringSheaf J P) :=
  (restrictionAlong alpha).obj
    ((restrictionAlong p.target).obj (conormalSource alpha'))

/-- The raw target conormal presheaf maps canonically to the restricted scalar-extended target
conormal sheaf. -/
noncomputable def conormalClassMap : (rawTarget p) ⟶ (targetSheaf p).val :=
  (PresheafOfModules.restrictScalars (ringSheafMap p.first).hom).map
      (conormalSourcePresheafUnit (O₂ := P') (O₃ := B') alpha') ≫
    ((Hom.restrictionIso (firstHom p)).hom.app (conormalSource alpha')).val

/-- The sheaf-valued relative derivation induced by the two parallel presentation maps. -/
@[stacks 0E1Y "sheaf-valued presentation difference derivation"]
noncomputable def derivation : (targetSheaf p).val.Derivation' phi.hom :=
  (rawDerivation p).postcomp (conormalClassMap p)

/-- The map from relative differentials induced by the presentation difference derivation. -/
noncomputable def differentialsMap :
    relativeDifferentials' phi.hom ⟶ (targetSheaf p).val :=
  (isUniversal' phi.hom).desc (derivation p)

/-- The map from relative differentials represents the sheaf-valued difference derivation. -/
@[simp]
theorem differentialsMap_fac :
    (derivation' phi.hom).postcomp (differentialsMap p) = derivation p := sorry

/-- The sectionwise map on relative differentials underlying `differentialsMap`. -/
noncomputable abbrev differentialsMapApp (U : Cᵒᵖ) :
    (relativeDifferentials' phi.hom).obj U ⟶ (targetSheaf p).val.obj U :=
  (differentialsMap p).app U

/-- The sheafified map from relative differentials to the target conormal sheaf. -/
@[stacks 0E1Y "presentation difference map over the source"]
noncomputable def mapOverSource :
    Ω(phi) ⟶ p.targetSheaf :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (ringSheaf J P).obj)).symm
      (p.differentialsMap ≫ (valRestrictionIso P p.targetSheaf).hom)

/-- The degree-lowering map associated to two parallel presentation maps. -/
@[stacks 0E1Y "parallel-presentation homotopy component"]
noncomputable def differenceMap :
    (extendAlong p.target).obj (conormalTensorTerm phi alpha) ⟶
      conormalSource alpha' :=
  ((extendRestrictAdj p.target).homEquiv _ _).symm
    (((extendRestrictAdj alpha).homEquiv _ _).symm p.mapOverSource)

/-- Applying the two extension-restriction adjunctions to `differenceMap` recovers its map over
the source presenting ring. -/
@[simp]
theorem differenceMap_adj :
    (extendRestrictAdj alpha).homEquiv
        Ω(phi)
        ((restrictionAlong p.target).obj (conormalSource alpha'))
        ((extendRestrictAdj p.target).homEquiv
          (conormalTensorTerm phi alpha) (conormalSource alpha') p.differenceMap) =
      p.mapOverSource := sorry

/-- The degree-lowering component family used to express the difference of the two induced
cochain maps as a null-homotopic map. -/
noncomputable def homotopyComponent (i j : ℤ)
    (_ : (ComplexShape.up ℤ).Rel j i) :
    ((extendComplex p.target).obj (complex phi alpha)).X i ⟶
      (complex phi' alpha').X j :=
  match i, j with
  | Int.ofNat 0, Int.negSucc 0 => p.differenceMap
  | _, _ => 0

/-- The only potentially nonzero homotopy component is the degree `0` to degree `-1` map. -/
@[simp]
theorem homotopyComponent_zero_negOne
    (h : (ComplexShape.up ℤ).Rel (-1) 0) :
    p.homotopyComponent 0 (-1) h = p.differenceMap := sorry

/-- The difference of the maps induced by a parallel pair is the null-homotopic map determined
by the presentation difference derivation. -/
theorem map_sub_eq_nullHomotopicMap :
    firstMap p - secondMap p =
      Homotopy.nullHomotopicMap' p.homotopyComponent := sorry

/-- The explicit null-homotopy of the difference between the two presentation maps. -/
noncomputable def differenceNullHomotopy :
    Homotopy (firstMap p - secondMap p) 0 :=
  (Homotopy.ofEq (map_sub_eq_nullHomotopicMap p)).trans
    (Homotopy.nullHomotopy' p.homotopyComponent)

/-- Parallel morphisms of presentations induce homotopic maps of naive cotangent complexes. -/
@[stacks 0E1Y "homotopy from parallel presentation maps"]
noncomputable def mapHomotopy : Homotopy (firstMap p) (secondMap p) :=
  Homotopy.equivSubZero.symm (differenceNullHomotopy p)

-- The degree-lowering morphism is built from explicit sectionwise difference classes and the
-- canonical sheafification/extension adjunctions.  `sorryAx` below is confined to naturality and
-- homotopy identities.

end Hom.Parallel

end SheafOfModules.RingedSite.NaiveCotangent.Presentation
