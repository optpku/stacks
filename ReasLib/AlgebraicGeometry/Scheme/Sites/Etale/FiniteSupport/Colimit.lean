/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Finite-support quotients and their colimit presentation

Supported sections on finite locally closed supports generate an abelian group
modulo addition and compatibility with enlargement of support.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.FiniteSupportColimit

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]

/-- A locally closed subset is eligible when it is the image of an immersion
whose composite to the base is finite. -/
def Eligible (V : Y.Etale) (Z : LocallyCloseds (baseChangeScheme f V)) : Prop :=
  ∃ (T : Scheme.{u}) (ι : T ⟶ baseChangeScheme f V),
    IsImmersion ι ∧ IsFinite (ι ≫ baseChangeToBase f V) ∧ Set.range ι = (Z : Set _)

/-- Finite supports with ambient opens in which they are closed, ordered by
enlarging the support and shrinking the ambient open. -/
abbrev Index (V : Y.Etale) :=
  {p : LocallyCloseds (baseChangeScheme f V) × OrderDual ((baseChangeScheme f V).Opens) //
    Eligible f V p.1 ∧
      (p.1 : Set (baseChangeScheme f V)) ⊆
        ((OrderDual.ofDual p.2 : (baseChangeScheme f V).Opens) : Set (baseChangeScheme f V)) ∧
      IsClosed ((OrderDual.ofDual p.2).ι ⁻¹' (p.1 : Set (baseChangeScheme f V)))}

namespace Index

variable {f} {V : Y.Etale}

/-- The locally closed support of an index. -/
abbrev subset (A : Index f V) : LocallyCloseds (baseChangeScheme f V) := A.val.1

/-- The ambient open of a support presentation. -/
abbrev ambient (A : Index f V) : (baseChangeScheme f V).Opens := OrderDual.ofDual A.val.2

omit [LocallyQuasiFinite f] in
/-- An index has an eligible support closed in its ambient open. -/
theorem spec (A : Index f V) : Eligible f V A.subset ∧
    (A.subset : Set (baseChangeScheme f V)) ⊆ A.ambient ∧
      IsClosed (A.ambient.ι ⁻¹' (A.subset : Set (baseChangeScheme f V))) :=
  A.property

omit [LocallyQuasiFinite f] in
/-- The support of an index is contained in its ambient open. -/
theorem subset_le_ambient (A : Index f V) :
    (A.subset : Set (baseChangeScheme f V)) ⊆ A.ambient :=
  A.property.2.1

omit [LocallyQuasiFinite f] in
/-- The support of an index is closed in its ambient open. -/
theorem isClosed_in_ambient (A : Index f V) :
    IsClosed (A.ambient.ι ⁻¹' (A.subset : Set _)) := A.property.2.2

omit [LocallyQuasiFinite f] in
/-- Index inequalities enlarge supports and shrink ambient opens. -/
theorem le_iff (A B : Index f V) :
    A ≤ B ↔ A.subset ≤ B.subset ∧ B.ambient ≤ A.ambient := Iff.rfl

/-- A geometric finite-support term determines its support presentation. -/
def ofTerm {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (t : FiniteSupportTerm f F V) : Index f V :=
  ⟨(t.locallyClosedSubset, OrderDual.toDual t.ambient),
    ⟨⟨t.subscheme, t.ι, t.ι_isImmersion, t.toBase_isFinite, rfl⟩,
      t.range_subset_ambient, t.isClosed_in_ambient⟩⟩

omit [LocallyQuasiFinite f] in
/-- The index of a finite-support term retains its support and ambient open. -/
theorem ofTerm_spec {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (t : FiniteSupportTerm f F V) :
    (ofTerm t).subset = t.locallyClosedSubset ∧ (ofTerm t).ambient = t.ambient :=
  ⟨rfl, rfl⟩

end Index

variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- The abelian group of sections supported on an indexed locally closed subset. -/
def sections {V : Y.Etale} (A : Index f V) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (sectionsSupportedIn F (baseChangeToSource f V) A.subset A.ambient
    A.subset_le_ambient A.isClosed_in_ambient)

omit [LocallyQuasiFinite f] in
/-- Membership in an indexed section group is containment of the support image. -/
theorem mem_sections_iff {V : Y.Etale} (A : Index f V)
    (s : F.1.obj (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))) :
    s ∈ sectionsSupportedIn F (baseChangeToSource f V) A.subset A.ambient
        A.subset_le_ambient A.isClosed_in_ambient ↔
      A.ambient.ι '' (abelianSheafSectionSupport F
        (mk (A.ambient.ι ≫ baseChangeToSource f V)) s :
          Set (mk (A.ambient.ι ≫ baseChangeToSource f V)).left) ⊆
        (A.subset : Set (baseChangeScheme f V)) :=
  mem_sectionsSupportedIn_iff F _ _ _ _ _ s

/-- An index inequality gives the inclusion of its smaller ambient open. -/
def ambientHom {V : Y.Etale} {A B : Index f V} (h : A ≤ B) :
    mk (B.ambient.ι ≫ baseChangeToSource f V) ⟶
      mk (A.ambient.ι ≫ baseChangeToSource f V) :=
  MorphismProperty.Over.homMk
    ((baseChangeScheme f V).homOfLE (U := B.ambient) (V := A.ambient) h.2)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k : B.ambient.toScheme ⟶ baseChangeScheme f V =>
        k ≫ baseChangeToSource f V)
        (Scheme.homOfLE_ι (baseChangeScheme f V) (U := B.ambient) (V := A.ambient) h.2)))

/-- Restriction along an index inequality preserves the enlarged support condition. -/
theorem restrict_mem {V : Y.Etale} {A B : Index f V} (h : A ≤ B)
    (s : sections f F A) :
    F.1.map (ambientHom f h).op s.val ∈
      sectionsSupportedIn F (baseChangeToSource f V) B.subset B.ambient
        B.subset_le_ambient B.isClosed_in_ambient := by
  sorry

/-- The supported-section map is the sheaf restriction along the ambient inclusion. -/
def sectionsMap {V : Y.Etale} {A B : Index f V} (h : A ≤ B) :
    sections f F A ⟶ sections f F B :=
  AddCommGrpCat.ofHom
    (((F.1.map (ambientHom f h).op).hom.restrict
      (sectionsSupportedIn F (baseChangeToSource f V) A.subset A.ambient
        A.subset_le_ambient A.isClosed_in_ambient)).codRestrict
      (sectionsSupportedIn F (baseChangeToSource f V) B.subset B.ambient
        B.subset_le_ambient B.isClosed_in_ambient) (restrict_mem f F h))

/-- The underlying section of a restriction is its sheaf restriction. -/
theorem sectionsMap_apply {V : Y.Etale} {A B : Index f V} (h : A ≤ B)
    (s : sections f F A) :
    (sectionsMap f F h s).val = F.1.map (ambientHom f h).op s.val := rfl

/-- Restriction along the identity inequality is the identity. -/
theorem sectionsMap_id {V : Y.Etale} (A : Index f V) :
    sectionsMap f F (le_refl A) = 𝟙 (sections f F A) := by
  sorry

/-- Successive restrictions agree with restriction along the composite inequality. -/
theorem sectionsMap_comp {V : Y.Etale} {A B C : Index f V} (h : A ≤ B) (k : B ≤ C) :
    sectionsMap f F (h.trans k) = sectionsMap f F h ≫ sectionsMap f F k := by
  sorry

/-- Restriction between ambient presentations of the same support is bijective. -/
theorem sectionsMap_bijective {V : Y.Etale} {A B : Index f V} (h : A ≤ B)
    (hZ : A.subset = B.subset) : Function.Bijective (sectionsMap f F h) := by
  sorry

/-- The diagram of groups of sections on finite locally closed supports. -/
def diagram (V : Y.Etale) : Index f V ⥤ AddCommGrpCat.{u} where
  obj := sections f F
  map h := sectionsMap f F (leOfHom h)
  map_id A := sectionsMap_id f F A
  map_comp h k := sectionsMap_comp f F (leOfHom h) (leOfHom k)

/-- The diagram evaluates to the indexed supported-section group. -/
theorem diagram_obj (V : Y.Etale) (A : Index f V) :
    (diagram f F V).obj A = sections f F A := rfl

/-- Generators are pairs of a finite support presentation and a supported section. -/
abbrev Generators (V : Y.Etale) := Σ A : Index f V, sections f F A

/-- The relations impose addition within each section group and compatibility
with each support enlargement. -/
def relations (V : Y.Etale) : AddSubgroup (FreeAbelianGroup (Generators f F V)) :=
  AddSubgroup.closure {x |
    (∃ (A : Index f V) (s t : sections f F A),
      x = FreeAbelianGroup.of ⟨A, s + t⟩ -
        FreeAbelianGroup.of ⟨A, s⟩ - FreeAbelianGroup.of ⟨A, t⟩) ∨
    (∃ (A B : Index f V) (h : A ≤ B) (s : sections f F A),
      x = FreeAbelianGroup.of ⟨A, s⟩ -
        FreeAbelianGroup.of ⟨B, sectionsMap f F h s⟩)}

/-- The finite-support group is the free abelian group modulo addition and
support-enlargement relations. -/
def group (V : Y.Etale) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (FreeAbelianGroup (Generators f F V) ⧸ relations f F V)

/-- A supported section defines its generator in the finite-support quotient. -/
def generator {V : Y.Etale} (A : Index f V) (s : sections f F A) : group f F V :=
  QuotientAddGroup.mk' (relations f F V) (FreeAbelianGroup.of ⟨A, s⟩)

/-- The zero supported section represents zero in the quotient. -/
theorem generator_zero {V : Y.Etale} (A : Index f V) :
    generator f F A 0 = 0 := by
  sorry

/-- Adding supported sections adds their quotient generators. -/
theorem generator_add {V : Y.Etale} (A : Index f V) (s t : sections f F A) :
    generator f F A (s + t) = generator f F A s + generator f F A t := by
  sorry

/-- A supported section and its image under support enlargement have the same class. -/
theorem generator_enlargement {V : Y.Etale} {A B : Index f V} (h : A ≤ B)
    (s : sections f F A) : generator f F B (sectionsMap f F h s) = generator f F A s := by
  sorry

/-- The inclusion of each supported-section group in the quotient is additive. -/
def inclusion {V : Y.Etale} (A : Index f V) : sections f F A ⟶ group f F V :=
  AddCommGrpCat.ofHom
    { toFun := generator f F A
      map_zero' := generator_zero f F A
      map_add' := generator_add f F A }

/-- The supported-section inclusions form a cocone with vertex the quotient. -/
def cocone (V : Y.Etale) : Cocone (diagram f F V) where
  pt := group f F V
  ι :=
    { app := inclusion f F
      naturality := fun A B h => by
        ext s
        exact generator_enlargement f F (leOfHom h) s }

/-- The free additive map sends a supported-section generator to its colimit coprojection. -/
def freeToColimit (V : Y.Etale) :
    FreeAbelianGroup (Generators f F V) →+ ↥(colimit (diagram f F V)) :=
  FreeAbelianGroup.lift (fun p => colimit.ι (diagram f F V) p.1 p.2)

/-- Addition and support-enlargement relations vanish under the colimit map. -/
theorem relations_le_ker (V : Y.Etale) :
    relations f F V ≤ (freeToColimit f F V).ker := by
  sorry

/-- The canonical map from the finite-support quotient to the supported-section colimit. -/
def toColimit (V : Y.Etale) : group f F V ⟶ colimit (diagram f F V) :=
  AddCommGrpCat.ofHom (QuotientAddGroup.lift (relations f F V)
    (freeToColimit f F V) (relations_le_ker f F V))

/-- Colimit descent of the quotient cocone gives the reverse comparison map. -/
def fromColimit (V : Y.Etale) : colimit (diagram f F V) ⟶ group f F V :=
  colimit.desc (diagram f F V) (cocone f F V)

/-- The comparison followed by its reverse is the identity on the quotient. -/
theorem iso_hom_inv_id (V : Y.Etale) :
    toColimit f F V ≫ fromColimit f F V = 𝟙 (group f F V) := by
  sorry

/-- The reverse comparison followed by the comparison is the identity on the colimit. -/
theorem iso_inv_hom_id (V : Y.Etale) :
    fromColimit f F V ≫ toColimit f F V = 𝟙 (colimit (diagram f F V)) := by
  sorry

/-- The finite-support quotient is canonically isomorphic to the colimit of
its supported-section groups. -/
def groupIsoColimit (V : Y.Etale) : group f F V ≅ colimit (diagram f F V) where
  hom := toColimit f F V
  inv := fromColimit f F V
  hom_inv_id := iso_hom_inv_id f F V
  inv_hom_id := iso_inv_hom_id f F V

/-- The canonical isomorphism sends each quotient generator to its colimit coprojection. -/
theorem groupIsoColimit_hom_generator {V : Y.Etale} (A : Index f V) (s : sections f F A) :
    (groupIsoColimit f F V).hom (generator f F A s) = colimit.ι (diagram f F V) A s := by
  sorry

/-- A geometric finite-support term defines a generator of the quotient. -/
def ofTerm {V : Y.Etale} (t : FiniteSupportTerm f F V) : group f F V :=
  generator f F (Index.ofTerm t) ⟨t.sec, t.mem_sectionsSupportedIn⟩

/-- The class of a geometric finite-support term is its supported-section generator. -/
theorem ofTerm_eq {V : Y.Etale} (t : FiniteSupportTerm f F V) :
    ofTerm f F t = generator f F (Index.ofTerm t) ⟨t.sec, t.mem_sectionsSupportedIn⟩ := rfl

/-- Finite formal sums map additively to the finite-support quotient. -/
def ofFormalSum (V : Y.Etale) : FiniteSupportFormalSum f F V →+ group f F V :=
  FreeAbelianGroup.lift (ofTerm f F)

/-- The formal-sum map sends a single term to its quotient generator. -/
theorem ofFormalSum_of {V : Y.Etale} (t : FiniteSupportTerm f F V) :
    ofFormalSum f F V (FreeAbelianGroup.of t) = ofTerm f F t :=
  FreeAbelianGroup.lift_apply_of _ _

/-- Every finite-support quotient class is represented by a geometric formal sum. -/
theorem ofFormalSum_surjective (V : Y.Etale) :
    Function.Surjective (ofFormalSum f F V) := by
  sorry

end AlgebraicGeometry.Scheme.Etale.FiniteSupportColimit

end
