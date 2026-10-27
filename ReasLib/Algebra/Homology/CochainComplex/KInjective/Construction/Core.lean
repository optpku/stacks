/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import ReasLib.CategoryTheory.Subobject.Cardinal
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.FunctorialResolution

/-! # Actual tests for unbounded K-injective replacement

The uniform bound is computed from the supplied Grothendieck category's actual separator.
Terms of test complexes are quotients of one specified coproduct of that separator. The codes
form a type in the original colimit universe: no representative family is selected from an
admitted existence or essential-smallness assertion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe w v u

namespace CochainComplex.KInjectiveResolution.Construction

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

-- Local instance justification (instance diamond): Mathlib deliberately leaves Abelian.hasFiniteBiproducts unregistered globally because of inference conflicts; this local registration supplies the native mapping-cone biproducts.
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The separator already supplied by the original Grothendieck-category certificate. -/
def generator : C := CategoryTheory.separator C

/-- The coproduct of `κ` copies of the separator. -/
def generatorCopies (κ : Cardinal.{w}) : C := ∐ fun _ : κ.out ↦ generator C

/-- The cardinal growth function counts subobjects of a coproduct of separators. -/
def growth (κ : Cardinal.{w}) : Cardinal.{w} :=
  Subobject.smallCardinal.{w} (generatorCopies C κ)

/-- The finite iterates of the cardinal growth function. -/
def cardinalStage : ℕ → Cardinal.{w}
  | 0 => Subobject.smallCardinal.{w} (generator C)
  | n + 1 => growth C (cardinalStage n)

/-- A countable sum bounds every finite iterate; the added countable cardinal handles degrees. -/
def bound : Cardinal.{w} := Cardinal.aleph0 + Cardinal.sum (cardinalStage C)

/-- An actual code for the kernel of a quotient of the fixed generator coproduct. -/
abbrev TermCode : Type w := Shrink.{w} (Subobject (generatorCopies C (bound C)))

/-- The kernel subobject named by a term code. -/
def termSubobject (s : TermCode C) : Subobject (generatorCopies C (bound C)) :=
  (equivShrink (Subobject (generatorCopies C (bound C)))).symm s

/-- The term itself is the native cokernel of its coded kernel inclusion. -/
def term (s : TermCode C) : C := cokernel (termSubobject C s).arrow

/-- Morphism codes use the original locally small Hom types, with their actual equivalence. -/
abbrev HomCode (s t : TermCode C) : Type w := Shrink.{w} (term C s ⟶ term C t)

/-- Decode the given small Hom code; no existence statement supplies this morphism. -/
def decodeHom {s t : TermCode C} (a : HomCode C s t) : term C s ⟶ term C t :=
  (equivShrink (term C s ⟶ term C t)).symm a

/-- Literal coded terms and differentials of a cochain complex, including square-zero laws. -/
structure ComplexCode : Type w where
  terms : ℤ → TermCode C
  differential : ∀ n : ℤ, HomCode C (terms n) (terms (n + 1))
  squareZero (n : ℤ) :
    decodeHom C (differential n) ≫ decodeHom C (differential (n + 1)) = 0

/-- The cochain complex with precisely the coded quotient objects and coded differential maps. -/
def ComplexCode.complex (c : ComplexCode C) : CochainComplex C ℤ :=
  CochainComplex.of (fun n ↦ term C (c.terms n))
    (fun n ↦ decodeHom C (c.differential n)) c.squareZero

/-- The actual original-universe family of bounded-above acyclic coded complexes. -/
def TestCode : Type w :=
  {c : ComplexCode C // c.complex.Acyclic ∧ ∃ n : ℤ, c.complex.IsStrictlyLE n}

/-- The complex represented by a particular member of the explicit test family. -/
def testComplex (c : TestCode C) : CochainComplex C ℤ := c.val.complex

/-- The null-homotopy target is the native mapping cone of the identity of the given test. -/
def testCone (c : TestCode C) : CochainComplex C ℤ :=
  CochainComplex.mappingCone (𝟙 (testComplex C c))

/-- The inclusion of a coded acyclic complex into the cone of its identity. -/
def testInclusion (c : TestCode C) : testComplex C c ⟶ testCone C c :=
  CochainComplex.mappingCone.inr (𝟙 (testComplex C c))

/-- The test source is acyclic by the original code's stored condition. -/
theorem testComplex_acyclic (c : TestCode C) : (testComplex C c).Acyclic := c.property.1

/-- The cone attachment is monomorphic degree by degree. -/
theorem testInclusion_mono (c : TestCode C) : _root_.CategoryTheory.Mono (testInclusion C c) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  apply mono_of_mono_fac
    (HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom
      (𝟙 (testComplex C c)) (n + 1) n rfl)

/-- Both the coded source and its identity cone are acyclic, so the inclusion is a quasi-isomorphism. -/
theorem testInclusion_quasiIso (c : TestCode C) : QuasiIso (testInclusion C c) := by
  rw [quasiIso_iff]
  intro n
  apply (quasiIsoAt_iff_exactAt _ n
    (testComplex_acyclic C c n)).mpr
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  simpa only [testCone, HomologicalComplex.homologyMap_id, HomologicalComplex.homologyMap_zero] using
    (mappingCone.homotopyToZeroOfId (testComplex C c)).homologyMap_eq n

/-- The native two-term contractible disk corepresenting evaluation in degree `n`. -/
def disk (A : C) (n : ℤ) : CochainComplex C ℤ :=
  HomologicalComplex.double (𝟙 A) (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)

/-- A specified object map induces the disk map through the native evaluation Hom correspondence. -/
def diskMap {A B : C} (a : A ⟶ B) (n : ℤ) : disk C A n ⟶ disk C B n :=
  (HomologicalComplex.evalCompCoyonedaCorepresentableByDoubleId
    (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) (by omega) A).homEquiv.symm
    (a ≫ (HomologicalComplex.doubleXIso₀ (𝟙 B)
      (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)).inv)

/-- The native correspondence between disk maps and a chosen degree component. -/
def diskHomEquiv (A : C) (n : ℤ) (I : CochainComplex C ℤ) :
    (disk C A n ⟶ I) ≃ (A ⟶ I.X n) :=
  (HomologicalComplex.evalCompCoyonedaCorepresentableByDoubleId
    (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) (by omega) A).homEquiv

omit [IsGrothendieckAbelian.{w} C] in
/-- Disk evaluation carries precomposition by an object map to the same precomposition. -/
@[simp]
lemma diskHomEquiv_diskMap_comp {A B : C} (a : A ⟶ B) (n : ℤ)
    {I : CochainComplex C ℤ} (f : disk C B n ⟶ I) :
    diskHomEquiv C A n I (diskMap C a n ≫ f) =
      a ≫ diskHomEquiv C B n I f := by
  change (HomologicalComplex.evalCompCoyonedaCorepresentableByDoubleId
    (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) (by omega) A).homEquiv
      (diskMap C a n ≫ f) = _
  rw [Functor.CorepresentableBy.homEquiv_comp]
  simp only [diskMap, Equiv.apply_symm_apply]
  change (a ≫ (HomologicalComplex.doubleXIso₀ (𝟙 B)
    (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)).inv) ≫ f.f n =
      a ≫ (HomologicalComplex.doubleXIso₀ (𝟙 B)
    (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)).inv ≫ f.f n
  exact Category.assoc _ _ _

/-- Actual small codes for the subobject inclusions used by the generator injectivity criterion. -/
abbrev GeneratorSubobjectCode : Type w := Shrink.{w} (Subobject (generator C))

/-- Decode the supplied subobject, retaining its actual native inclusion. -/
def generatorSubobject (s : GeneratorSubobjectCode C) : Subobject (generator C) :=
  (equivShrink (Subobject (generator C))).symm s

/-- The term-injectivity attachment is the disk image of a specified generator-subobject inclusion. -/
def generatorDiskMap (n : ℤ) (s : GeneratorSubobjectCode C) :
    disk C (generatorSubobject C s) n ⟶ disk C (generator C) n :=
  diskMap C (generatorSubobject C s).arrow n

private lemma generatorDiskMap_degree_succ (n : ℤ) (s : GeneratorSubobjectCode C) :
    Mono ((generatorDiskMap C n s).f (n + 1)) := by
  simp only [generatorDiskMap, diskMap,
    HomologicalComplex.evalCompCoyonedaCorepresentableByDoubleId, Equiv.symm,
    Equiv.coe_fn_mk, HomologicalComplex.mkHomFromDouble_f₁]
  dsimp only [disk]
  rw [HomologicalComplex.double_d _ _ (by omega)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.id_comp]
  infer_instance

/-- The given generator subobject has a monomorphic disk inclusion. -/
theorem generatorDiskMap_mono (n : ℤ) (s : GeneratorSubobjectCode C) :
    _root_.CategoryTheory.Mono (generatorDiskMap C n s) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  by_cases hi : i = n
  · subst i
    simp only [generatorDiskMap, diskMap,
      HomologicalComplex.evalCompCoyonedaCorepresentableByDoubleId, Equiv.symm,
      Equiv.coe_fn_mk, HomologicalComplex.mkHomFromDouble_f₀]
    infer_instance
  · by_cases hi' : i = n + 1
    · subst i
      exact generatorDiskMap_degree_succ C n s
    · exact (HomologicalComplex.isZero_double_X _ _ i hi hi').mono _

private lemma disk_acyclic (A : C) (n : ℤ) : (disk C A n).Acyclic := by
  intro i
  by_cases hi : i = n
  · subst i
    rw [(disk C A n).exactAt_iff' (j := n) (i := n - 1) (k := n + 1)
      (by simp) (by simp)]
    apply (ShortComplex.exact_iff_mono _ (by
      change (disk C A n).d (n - 1) n = 0
      exact HomologicalComplex.double_d_eq_zero₀ (𝟙 A)
        (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) _ _ (by omega))).mpr
    change Mono ((disk C A n).d n (n + 1))
    dsimp only [disk]
    rw [HomologicalComplex.double_d _ _ (by omega)]
    infer_instance
  · by_cases hi' : i = n + 1
    · subst i
      rw [(disk C A n).exactAt_iff' (j := n + 1) (i := n) (k := n + 1 + 1)
        (by simp) (by simp)]
      apply (ShortComplex.exact_iff_epi _ (by
        change (disk C A n).d (n + 1) (n + 1 + 1) = 0
        exact HomologicalComplex.double_d_eq_zero₀ (𝟙 A)
          (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl) _ _ (by omega))).mpr
      change Epi ((disk C A n).d n (n + 1))
      dsimp only [disk]
      rw [HomologicalComplex.double_d _ _ (by omega)]
      infer_instance
    · exact HomologicalComplex.ExactAt.of_isZero
        (HomologicalComplex.isZero_double_X _ _ i hi hi')

/-- Both disks are contractible, so their specified map is a quasi-isomorphism. -/
theorem generatorDiskMap_quasiIso (n : ℤ) (s : GeneratorSubobjectCode C) :
    QuasiIso (generatorDiskMap C n s) := by
  rw [quasiIso_iff]
  intro i
  exact (quasiIsoAt_iff_exactAt _ i (disk_acyclic C _ n i)).mpr (disk_acyclic C _ n i)

/-- The explicit small index includes both null-homotopy and term-injectivity attachments. -/
abbrev AttachmentIndex : Type w := TestCode C ⊕ (ℤ × GeneratorSubobjectCode C)

/-- The actual domain of a specified attachment. -/
def attachmentSource : AttachmentIndex C → CochainComplex C ℤ
  | .inl c => testComplex C c
  | .inr p => disk C (generatorSubobject C p.2) p.1

/-- The actual target of the same attachment. -/
def attachmentTarget : AttachmentIndex C → CochainComplex C ℤ
  | .inl c => testCone C c
  | .inr p => disk C (generator C) p.1

/-- The actual generating arrow, with no morphism chosen from an existence assertion. -/
def attachment : ∀ i : AttachmentIndex C, attachmentSource C i ⟶ attachmentTarget C i
  | .inl c => testInclusion C c
  | .inr p => generatorDiskMap C p.1 p.2

/-- Each specified attachment is monomorphic. -/
theorem attachment_mono (i : AttachmentIndex C) : _root_.CategoryTheory.Mono (attachment C i) := by
  cases i with
  | inl c => exact testInclusion_mono C c
  | inr p => exact generatorDiskMap_mono C p.1 p.2

/-- Every attachment is acyclic; thus transfinite attachment preserves quasi-isomorphisms. -/
theorem attachment_quasiIso (i : AttachmentIndex C) : QuasiIso (attachment C i) := by
  cases i with
  | inl c => exact testInclusion_quasiIso C c
  | inr p => exact generatorDiskMap_quasiIso C p.1 p.2

/-- The generating morphism property is the native property of this actual small family. -/
def generatingMaps : MorphismProperty (CochainComplex C ℤ) :=
  MorphismProperty.ofHoms (attachment C)

/-- The actual generating family is small in the specified universe. -/
instance generatingMaps_small : MorphismProperty.IsSmall.{w} (generatingMaps C) := by
  dsimp [generatingMaps]
  infer_instance

/-- The actual small disjoint union of all domain-subobject lattices determines a regular bound. -/
abbrev DomainSubobjectCode : Type w :=
  Σ i : AttachmentIndex C, Shrink.{w} (Subobject (attachmentSource C i))

/-- This specific regular successor is the iteration length of the native small object argument. -/
def iterationCardinal : Cardinal.{w} :=
  Order.succ (max (Cardinal.mk (DomainSubobjectCode C)) Cardinal.aleph0)

/-- The specified successor cardinal is regular. -/
instance iterationCardinal_isRegular : Fact (iterationCardinal C).IsRegular :=
  ⟨Cardinal.isRegular_succ (le_max_right _ _)⟩

/-- The actual ordinal iteration index is nonempty by regularity of the specified cardinal. -/
instance iterationIndex_nonempty : Nonempty (iterationCardinal C).ord.ToType := by
  simpa using (iterationCardinal_isRegular C).out.ne_zero

/-- Use the native least element of this actual well-ordered ordinal index. -/
instance iterationIndex_orderBot : OrderBot (iterationCardinal C).ord.ToType :=
  WellFoundedLT.toOrderBot _

/-- Each given generating domain is small for the specified transfinite monomorphism tower.
The bound counts its whole subobject lattice, in the original colimit universe. -/
theorem attachmentSource_preservesColimit
    {A B X Y : CochainComplex C ℤ} (i : A ⟶ B) (hi : generatingMaps C i) (f : X ⟶ Y)
    (hf : HomotopicalAlgebra.RelativeCellComplex.{w}
      (fun (_ : (iterationCardinal C).ord.ToType) ↦ (generatingMaps C).homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (Opposite.op A)) := by
  have hDomain : HasCardinalLT (DomainSubobjectCode C) (iterationCardinal C) := by
    rw [hasCardinalLT_iff_cardinal_mk_lt]
    change Cardinal.mk (DomainSubobjectCode C) <
      Order.succ (max (Cardinal.mk (DomainSubobjectCode C)) Cardinal.aleph0)
    exact lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ _)
  have sourceBound (k : AttachmentIndex C) :
      HasCardinalLT (Subobject (attachmentSource C k)) (iterationCardinal C) := by
    apply hDomain.of_injective
      (fun s : Subobject (attachmentSource C k) ↦
        (⟨k, (equivShrink (Subobject (attachmentSource C k))) s⟩ : DomainSubobjectCode C))
    intro a b h
    have h' : HEq (equivShrink (Subobject (attachmentSource C k)) a)
        (equivShrink (Subobject (attachmentSource C k)) b) :=
      (Sigma.mk.inj_iff.mp h).2
    exact (equivShrink (Subobject (attachmentSource C k))).injective (eq_of_heq h')
  let hf' :
      (MorphismProperty.monomorphisms (CochainComplex C ℤ)).TransfiniteCompositionOfShape
        (iterationCardinal C).ord.ToType f :=
    { toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
      map_mem j hj := by
        have h := (hf.attachCells j hj).pushouts_coproducts
        simp only [MorphismProperty.ofHoms_homFamily] at h
        refine (?_ : _ ≤ MorphismProperty.monomorphisms _) _ h
        simp only [MorphismProperty.pushouts_le_iff, MorphismProperty.coproducts_le_iff]
        change MorphismProperty.ofHoms (attachment C) ≤ _
        rw [MorphismProperty.ofHoms_le_iff]
        intro k
        exact attachment_mono C k
    }
  -- Local instance justification (proof-local temporary data): The explicit transfinite monomorphism tower supplies the mapwise monomorphism evidence required by the native coyoneda colimit theorem.
  letI (j j' : (iterationCardinal C).ord.ToType) (φ : j ⟶ j') :
      Mono (hf'.F.map φ) := hf'.mem_map φ
  obtain ⟨k, hk⟩ := (MorphismProperty.ofHoms_iff (attachment C) i).1 hi
  obtain ⟨hA, _hB, _hi⟩ := (Arrow.mk_eq_mk_iff i (attachment C k)).1 hk
  apply CategoryTheory.IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono
    (Y := hf'.F) (κ := iterationCardinal C)
  rw [hA]
  exact sourceBound k

/-- The cardinal witness stores this actual family, actual colimits and actual regular ordinal.
The native colimit-preservation certificate is supplied for every displayed monomorphism tower. -/
instance iterationCardinal_isCardinalForSmallObjectArgument :
    (generatingMaps C).IsCardinalForSmallObjectArgument (iterationCardinal C) where
  preservesColimit i hi f hf := attachmentSource_preservesColimit C i hi f hf

/-- The native transfinite pushout construction supplies every factor object and every map. -/
def factorization :
    MorphismProperty.FunctorialFactorizationData
      (generatingMaps C).rlp.llp (generatingMaps C).rlp :=
  CategoryTheory.SmallObject.functorialFactorizationData (generatingMaps C) (iterationCardinal C)

set_option backward.isDefEq.respectTransparency false in
/-- The actual zero-arrow functor retains the original input and each original complex map. -/
def zeroArrow : CochainComplex C ℤ ⥤ Arrow (CochainComplex C ℤ) where
  obj K := Arrow.mk (0 : K ⟶ (HomologicalComplex.zero : CochainComplex C ℤ))
  map a := Arrow.homMk a (𝟙 _) (by simp)
  map_id := by intro K; rfl
  map_comp := by intro K L M a b; ext <;> simp

/-- The replacement is the actual intermediate-object functor in the specified factorization. -/
def replacement : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  zeroArrow C ⋙ (factorization C).Z

/-- The comparison is the specified first arrow of the same native factorization. -/
def augmentation : 𝟭 (CochainComplex C ℤ) ⟶ replacement C where
  app K := (factorization C).i.app ((zeroArrow C).obj K)
  naturality _ _ a := (factorization C).i.naturality ((zeroArrow C).map a)

/-- A transfinite composite of the specified acyclic monomorphisms is monomorphic. -/
theorem augmentation_mono (K : CochainComplex C ℤ) :
    _root_.CategoryTheory.Mono ((augmentation C).app K) := by
  have hgen : generatingMaps C ≤ MorphismProperty.monomorphisms (CochainComplex C ℤ) := by
    rw [generatingMaps, MorphismProperty.ofHoms_le_iff]
    intro i
    exact attachment_mono C i
  have h := (factorization C).hi ((zeroArrow C).obj K)
  have hle := MorphismProperty.antitone_llp (MorphismProperty.antitone_rlp hgen)
  rw [CategoryTheory.IsGrothendieckAbelian.llp_rlp_monomorphisms
    (isSeparator_separator (CochainComplex C ℤ))] at hle
  exact hle _ h

private def degreeDiagram {D : Type w} [Category.{w} D]
    (F : D ⥤ CochainComplex C ℤ) (i : ℤ) : ShortComplex (D ⥤ C) :=
  (ShortComplex.functorEquivalence D C).inverse.obj
    (F ⋙ HomologicalComplex.shortComplexFunctor C (.up ℤ) i)

private def degreeColimitIso {D : Type w} [Category.{w} D]
    (F : D ⥤ CochainComplex C ℤ) (c : Cocone F) (hc : IsColimit c) (i : ℤ) :
    ((degreeDiagram C F i).map (colim (J := D))) ≅ c.pt.sc i := by
  refine ShortComplex.isoMk
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) ((ComplexShape.up ℤ).prev i)) hc))
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) i) hc))
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) ((ComplexShape.up ℤ).next i)) hc))
    ?_ ?_
  · apply colimit.hom_ext
    intro j
    change colimit.ι (F ⋙ HomologicalComplex.eval C (.up ℤ) ((ComplexShape.up ℤ).prev i)) j ≫
      _ ≫ _ = colimit.ι (F ⋙ HomologicalComplex.eval C (.up ℤ) ((ComplexShape.up ℤ).prev i)) j ≫
      colim.map _ ≫ _
    erw [← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom,
      ι_colimMap_assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact (c.ι.app j).comm _ _
  · apply colimit.hom_ext
    intro j
    change colimit.ι (F ⋙ HomologicalComplex.eval C (.up ℤ) i) j ≫
      _ ≫ _ = colimit.ι (F ⋙ HomologicalComplex.eval C (.up ℤ) i) j ≫ colim.map _ ≫ _
    erw [← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom,
      ι_colimMap_assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact (c.ι.app j).comm _ _

private lemma quasiIso_colimit {D : Type w} [Category.{w} D]
    [HasExactColimitsOfShape D C]
    {F G : D ⥤ CochainComplex C ℤ} (φ : F ⟶ G)
    (hφ : ∀ j, QuasiIso (φ.app j))
    (cF : Cocone F) (hcF : IsColimit cF) (cG : Cocone G) (hcG : IsColimit cG)
    (f : cF.pt ⟶ cG.pt)
    (hf : ∀ j, cF.ι.app j ≫ f = φ.app j ≫ cG.ι.app j) : QuasiIso f := by
  rw [quasiIso_iff]
  intro i
  let ψ : degreeDiagram C F i ⟶ degreeDiagram C G i :=
    (ShortComplex.functorEquivalence D C).inverse.map
      (Functor.whiskerRight φ (HomologicalComplex.shortComplexFunctor C (.up ℤ) i))
  have hj (j : D) : ShortComplex.QuasiIso
      (((evaluation D C).obj j).mapShortComplex.map ψ) :=
    (quasiIsoAt_iff _ i).mp ((hφ j).quasiIsoAt i)
  have hψ : ShortComplex.QuasiIso ψ := by
    rw [ShortComplex.quasiIso_iff]
    have hj' (j : D) : IsIso ((ShortComplex.homologyMap ψ).app j) := by
      -- Local instance justification (proof-local temporary data): The component quasi-isomorphism is required by the evaluation and homology comparison at this fixed diagram object.
      haveI := hj j
      let e := (degreeDiagram C F i).mapHomologyIso ((evaluation D C).obj j)
      -- Local instance justification (proof-local temporary data): This comparison composite is invertible at the fixed component, allowing cancellation of e.hom.
      haveI : IsIso (e.hom ≫ (ShortComplex.homologyMap ψ).app j) := by
        change IsIso (((degreeDiagram C F i).mapHomologyIso ((evaluation D C).obj j)).hom ≫
          ((evaluation D C).obj j).map (ShortComplex.homologyMap ψ))
        rw [← ShortComplex.mapHomologyIso_hom_naturality ψ ((evaluation D C).obj j)]
        infer_instance
      exact IsIso.of_isIso_comp_left e.hom _
    exact NatIso.isIso_of_isIso_app _
  -- Local instance justification (proof-local temporary data): Preservation of homology by the colimit consumes the just-proved quasi-isomorphism of the diagram short complexes.
  haveI := hψ
  -- Local instance justification (proof-local temporary data): The fixed colimit comparison is a quasi-isomorphism, which is transported to f by the displayed arrow isomorphism.
  haveI : ShortComplex.QuasiIso ((colim (J := D)).mapShortComplex.map ψ) :=
    ShortComplex.quasiIso_map_of_preservesLeftHomology _ ψ
  apply (quasiIsoAt_iff f i).mpr
  apply ShortComplex.quasiIso_of_arrow_mk_iso
    ((colim (J := D)).mapShortComplex.map ψ)
  refine Arrow.isoMk (degreeColimitIso C F cF hcF i) (degreeColimitIso C G cG hcG i) ?_
  have he (k : ℤ) :
      (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
        (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) k) hcF)).hom ≫ f.f k =
      colim.map (Functor.whiskerRight φ (HomologicalComplex.eval C (.up ℤ) k)) ≫
        (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
          (isColimitOfPreserves (HomologicalComplex.eval C (.up ℤ) k) hcG)).hom := by
    apply colimit.hom_ext
    intro j
    erw [← Category.assoc, IsColimit.comp_coconePointUniqueUpToIso_hom,
      ι_colimMap_assoc, IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact congrArg (fun a ↦ a.f k) (hf j)
  ext
  all_goals exact he _

private lemma quasiIso_of_acyclic_cokernel {A B : CochainComplex C ℤ}
    (f : A ⟶ B) [Mono f] (h : (cokernel f).Acyclic) : QuasiIso f := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ⟨ShortComplex.exact_cokernel f⟩
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  -- Local instance justification (proof-local temporary data): Exactness and vanishing of the adjacent cokernel homology make this particular homology map monomorphic.
  haveI : Mono (HomologicalComplex.homologyMap f i) :=
    (hS.homology_exact₁ (i - 1) i (by change i - 1 + 1 = i; omega)).mono_g
      ((h (i - 1)).isZero_homology.eq_of_src _ _)
  -- Local instance justification (proof-local temporary data): Vanishing of the cokernel-side homology makes this particular homology map epic.
  haveI : Epi (HomologicalComplex.homologyMap f i) :=
    (hS.homology_exact₂ i).epi_f ((h i).isZero_homology.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

private lemma quasiIso_pushout {A B A' B' : CochainComplex C ℤ}
    {f : A ⟶ B} {g : A ⟶ A'} {g' : B ⟶ B'} {f' : A' ⟶ B'}
    (sq : IsPushout f g g' f') [Mono f] (hf : QuasiIso f) : QuasiIso f' := by
  have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    ⟨ShortComplex.exact_cokernel f⟩
  have hQ := hS.acyclic_X₃ hf
  -- Local instance justification (proof-local temporary data): The given monomorphism remains monomorphic under this particular pushout.
  haveI : Mono f' := (MorphismProperty.monomorphisms _).of_isPushout sq.flip
    (inferInstanceAs (Mono f))
  -- Local instance justification (proof-local temporary data): The canonical cokernel comparison for this pushout is invertible and transports acyclicity to its cokernel.
  haveI := isIso_cokernel_map_of_isPushout sq
  apply quasiIso_of_acyclic_cokernel C f'
  intro i
  exact (hQ i).of_iso (asIso (cokernel.map _ _ _ _ sq.w))

private lemma quasiIso_colimit_stable (D : Type w) [Category.{w} D]
    [HasExactColimitsOfShape D C] :
    (HomologicalComplex.quasiIso C (.up ℤ)).IsStableUnderColimitsOfShape D where
  condition F G cF cG hcF hcG φ hφ f hf :=
    quasiIso_colimit C φ hφ cF hcF cG hcG f hf

/-- Filtered colimits are exact, so this actual transfinite attachment remains a quasi-isomorphism. -/
theorem augmentation_quasiIso (K : CochainComplex C ℤ) : QuasiIso ((augmentation C).app K) := by
  let W : MorphismProperty (CochainComplex C ℤ) :=
    HomologicalComplex.quasiIso C (.up ℤ) ⊓ MorphismProperty.monomorphisms _
  -- Local instance justification (proof-local temporary data): The proof-local intersection W of quasi-isomorphisms and monomorphisms needs cobase-change closure for the transfinite-composition theorem.
  haveI : W.IsStableUnderCobaseChange := ⟨fun sq hf ↦ by
    -- Local instance justification (proof-local temporary data): Membership of this particular arrow in W supplies the Mono premise consumed by quasiIso_pushout.
    haveI := hf.2
    exact ⟨quasiIso_pushout C sq.flip hf.1,
      (MorphismProperty.monomorphisms _).of_isPushout sq hf.2⟩⟩
  -- Local instance justification (proof-local temporary data): Exact coproducts give the quasi-isomorphism closure certificate needed to assemble coproduct closure of this W.
  haveI : (HomologicalComplex.quasiIso C (.up ℤ)).IsStableUnderCoproducts.{w} := {
    isStableUnderCoproductsOfShape J := quasiIso_colimit_stable C (Discrete J) }
  -- Local instance justification (proof-local temporary data): The displayed proof-local intersection W needs its combined coproduct-closure certificate for the small-object argument.
  haveI : W.IsStableUnderCoproducts.{w} := {
    isStableUnderCoproductsOfShape J := by
      constructor
      intro F G cF cG hcF hcG φ hφ f hf
      exact ⟨quasiIso_colimit C φ (fun j ↦ (hφ j).1) cF hcF cG hcG f hf,
        MorphismProperty.IsStableUnderColimitsOfShape.condition
          (W := MorphismProperty.monomorphisms _) F G cF cG hcF hcG φ
          (fun j ↦ (hφ j).2) f hf⟩ }
  -- Local instance justification (proof-local temporary data): Exact filtered colimits give the quasi-isomorphism closure certificate needed to assemble filtered-colimit closure of W.
  haveI : (HomologicalComplex.quasiIso C (.up ℤ)).IsStableUnderFilteredColimits.{w, w} := {
    isStableUnderColimitsOfShape J := quasiIso_colimit_stable C J }
  -- Local instance justification (proof-local temporary data): This proof-local intersection W is closed under the filtered colimits used in the attachment tower.
  haveI : W.IsStableUnderFilteredColimits.{w, w} := {
    isStableUnderColimitsOfShape J := by
      intro instCategory instFiltered
      constructor
      intro F G cF cG hcF hcG φ hφ f hf
      exact ⟨quasiIso_colimit C φ (fun j ↦ (hφ j).1) cF hcF cG hcG f hf,
        MorphismProperty.IsStableUnderColimitsOfShape.condition
          (W := MorphismProperty.monomorphisms _) F G cF cG hcF hcG φ
          (fun j ↦ (hφ j).2) f hf⟩ }
  -- Local instance justification (proof-local temporary data): The native transfinite-composition theorem consumes multiplicativity of this particular intersection W.
  haveI : W.IsMultiplicative := by dsimp [W]; infer_instance
  -- Local instance justification (proof-local temporary data): The derived closure certificate for W at this fixed iteration ordinal is consumed by the transfinite attachment argument.
  haveI : W.IsStableUnderTransfiniteCompositionOfShape (iterationCardinal C).ord.ToType :=
    inferInstance
  have hgen : generatingMaps C ≤ W := by
    rw [generatingMaps, MorphismProperty.ofHoms_le_iff]
    exact fun i ↦ ⟨attachment_quasiIso C i, attachment_mono C i⟩
  have h := SmallObject.transfiniteCompositionsOfShape_ιObj
    (generatingMaps C) (iterationCardinal C) ((zeroArrow C).obj K).hom
  apply And.left (b := Mono ((augmentation C).app K))
  apply W.transfiniteCompositionsOfShape_le (iterationCardinal C).ord.ToType
  exact MorphismProperty.transfiniteCompositionsOfShape_monotone
    (iterationCardinal C).ord.ToType (by simpa only [MorphismProperty.pushouts_le_iff,
      MorphismProperty.coproducts_le_iff] using hgen) _ h

/-- A factorization lift against the specified disk gives an actual generator extension. -/
def generatorExtension (I : CochainComplex C ℤ)
    (hp : (generatingMaps C).rlp (0 : I ⟶ HomologicalComplex.zero))
    (n : ℤ) (s : GeneratorSubobjectCode C)
    (f : (generatorSubobject C s : C) ⟶ I.X n) : generator C ⟶ I.X n := by
  -- Local instance justification (proof-local temporary data): The supplied right lifting property specializes to this generator disk and is consumed by the native square lift.
  letI : HasLiftingProperty (generatorDiskMap C n s)
      (0 : I ⟶ HomologicalComplex.zero) :=
    hp (attachment C (.inr (n, s))) (by
      change MorphismProperty.ofHoms (attachment C) _
      exact ⟨Sum.inr (n, s)⟩)
  let sq : CommSq ((diskHomEquiv C _ n I).symm f)
      (generatorDiskMap C n s) (0 : I ⟶ HomologicalComplex.zero) 0 := ⟨by simp⟩
  exact diskHomEquiv C _ n I sq.lift

/-- The generator extension restricts to the prescribed map on its subobject. -/
@[reassoc]
lemma generatorExtension_fac (I : CochainComplex C ℤ)
    (hp : (generatingMaps C).rlp (0 : I ⟶ HomologicalComplex.zero))
    (n : ℤ) (s : GeneratorSubobjectCode C)
    (f : (generatorSubobject C s : C) ⟶ I.X n) :
    (generatorSubobject C s).arrow ≫ generatorExtension C I hp n s f = f := by
  -- Local instance justification (defeq pin): The factorization law must compute with exactly the lifting witness and square selected by generatorExtension.
  letI : HasLiftingProperty (generatorDiskMap C n s)
      (0 : I ⟶ HomologicalComplex.zero) :=
    hp (attachment C (.inr (n, s))) (by
      change MorphismProperty.ofHoms (attachment C) _
      exact ⟨Sum.inr (n, s)⟩)
  let sq : CommSq ((diskHomEquiv C _ n I).symm f)
      (generatorDiskMap C n s) (0 : I ⟶ HomologicalComplex.zero) 0 := ⟨by simp⟩
  change (generatorSubobject C s).arrow ≫ diskHomEquiv C _ n I sq.lift = f
  rw [← diskHomEquiv_diskMap_comp]
  change diskHomEquiv C _ n I (generatorDiskMap C n s ≫ sq.lift) = f
  rw [sq.fac_left, Equiv.apply_symm_apply]

/-- Native Baer criterion applied to the actual generator extensions. -/
theorem termInjective_of_generatingMaps_rlp (I : CochainComplex C ℤ)
    (hp : (generatingMaps C).rlp (0 : I ⟶ HomologicalComplex.zero)) (n : ℤ) :
    Injective (I.X n) := by
  rw [injective_iff_rlp_monomorphisms_zero,
    ← CategoryTheory.IsGrothendieckAbelian.generatingMonomorphisms_rlp
      (show IsSeparator (generator C) from isSeparator_separator C)]
  rintro A B i ⟨S⟩
  let s : GeneratorSubobjectCode C := equivShrink (Subobject (generator C)) S
  have hs : generatorSubobject C s = S := by simp [generatorSubobject, s]
  rw [← hs]
  refine ⟨?_⟩
  intro f g sq
  exact CommSq.HasLift.mk'
    { l := generatorExtension C I hp n s f
      fac_left := generatorExtension_fac C I hp n s f
      fac_right := (isZero_zero C).eq_of_tgt _ _ }

/-- The native factorization RLP applies to the unchanged replacement object. -/
theorem replacement_term_injective (K : CochainComplex C ℤ) (n : ℤ) :
    Injective (((replacement C).obj K).X n) := by
  apply termInjective_of_generatingMaps_rlp C _ _ n
  have h := (factorization C).hp ((zeroArrow C).obj K)
  have hz : (factorization C).p.app ((zeroArrow C).obj K) = 0 := by
    ext i
    exact (isZero_zero C).eq_of_tgt _ _
  rw [hz] at h
  exact h

end CochainComplex.KInjectiveResolution.Construction
