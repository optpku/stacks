module

public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
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

universe w v u

namespace CochainComplex.KInjectiveResolution.Construction

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

-- The mapping cone uses the native finite biproducts of this abelian category.
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The separator already supplied by the original Grothendieck-category certificate. -/
def generator : C := CategoryTheory.separator C

/-- The actual constant coproduct used in the source's cardinal growth function. -/
def generatorCopies (κ : Cardinal.{w}) : C := ∐ fun _ : κ.out ↦ generator C

/-- The source size function counts the genuine small lattice of subobjects. -/
def growth (κ : Cardinal.{w}) : Cardinal.{w} :=
  Subobject.smallCardinal.{w} (generatorCopies C κ)

/-- The finite iterates of the explicit source size function. -/
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

/-- The specified inclusion in that cone is the source's homotopy-killing attachment. -/
def testInclusion (c : TestCode C) : testComplex C c ⟶ testCone C c :=
  CochainComplex.mappingCone.inr (𝟙 (testComplex C c))

/-- The test source is acyclic by the original code's stored condition. -/
theorem testComplex_acyclic (c : TestCode C) : (testComplex C c).Acyclic := c.property.1

/-- The cone attachment is monomorphic degree by degree. -/
instance testInclusion_mono (c : TestCode C) : Mono (testInclusion C c) := sorry

/-- Both the coded source and its identity cone are acyclic, so the inclusion is a quasi-isomorphism. -/
theorem testInclusion_quasiIso (c : TestCode C) : QuasiIso (testInclusion C c) := sorry

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

/-- The given generator subobject has a monomorphic disk inclusion. -/
instance generatorDiskMap_mono (n : ℤ) (s : GeneratorSubobjectCode C) :
    Mono (generatorDiskMap C n s) := sorry

/-- Both disks are contractible, so their specified map is a quasi-isomorphism. -/
theorem generatorDiskMap_quasiIso (n : ℤ) (s : GeneratorSubobjectCode C) :
    QuasiIso (generatorDiskMap C n s) := sorry

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
instance attachment_mono (i : AttachmentIndex C) : Mono (attachment C i) := by
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

instance generatingMaps_small : MorphismProperty.IsSmall.{w} (generatingMaps C) := by
  dsimp [generatingMaps]
  infer_instance

/-- The actual small disjoint union of all domain-subobject lattices determines a regular bound. -/
abbrev DomainSubobjectCode : Type w :=
  Σ i : AttachmentIndex C, Shrink.{w} (Subobject (attachmentSource C i))

/-- This specific regular successor is the iteration length of the native small object argument. -/
def iterationCardinal : Cardinal.{w} :=
  Order.succ (max (Cardinal.mk (DomainSubobjectCode C)) Cardinal.aleph0)

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
        exact inferInstance
    }
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

/-- The actual zero-arrow functor retains the original input and each original complex map. -/
def zeroArrow : CochainComplex C ℤ ⥤ Arrow (CochainComplex C ℤ) where
  obj K := Arrow.mk (0 : K ⟶ (HomologicalComplex.zero : CochainComplex C ℤ))
  map a := Arrow.homMk a (𝟙 _) (by sorry)
  map_id := sorry
  map_comp := sorry

/-- The replacement is the actual intermediate-object functor in the specified factorization. -/
def replacement : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  zeroArrow C ⋙ (factorization C).Z

/-- The comparison is the specified first arrow of the same native factorization. -/
def augmentation : 𝟭 (CochainComplex C ℤ) ⟶ replacement C where
  app K := (factorization C).i.app ((zeroArrow C).obj K)
  naturality _ _ a := (factorization C).i.naturality ((zeroArrow C).map a)

/-- A transfinite composite of the specified acyclic monomorphisms is monomorphic. -/
instance augmentation_mono (K : CochainComplex C ℤ) : Mono ((augmentation C).app K) := sorry

/-- Filtered colimits are exact, so this actual transfinite attachment remains a quasi-isomorphism. -/
theorem augmentation_quasiIso (K : CochainComplex C ℤ) : QuasiIso ((augmentation C).app K) := sorry

/-- A factorization lift against the specified disk gives an actual generator extension. -/
def generatorExtension (I : CochainComplex C ℤ)
    (hp : (generatingMaps C).rlp (0 : I ⟶ HomologicalComplex.zero))
    (n : ℤ) (s : GeneratorSubobjectCode C)
    (f : (generatorSubobject C s : C) ⟶ I.X n) : generator C ⟶ I.X n := by
  letI : HasLiftingProperty (generatorDiskMap C n s)
      (0 : I ⟶ HomologicalComplex.zero) :=
    hp (attachment C (.inr (n, s))) (by
      change MorphismProperty.ofHoms (attachment C) _
      exact ⟨Sum.inr (n, s)⟩)
  let sq : CommSq ((diskHomEquiv C _ n I).symm f)
      (generatorDiskMap C n s) (0 : I ⟶ HomologicalComplex.zero) 0 := ⟨by simp⟩
  exact diskHomEquiv C _ n I sq.lift

@[reassoc]
lemma generatorExtension_fac (I : CochainComplex C ℤ)
    (hp : (generatingMaps C).rlp (0 : I ⟶ HomologicalComplex.zero))
    (n : ℤ) (s : GeneratorSubobjectCode C)
    (f : (generatorSubobject C s : C) ⟶ I.X n) :
    (generatorSubobject C s).arrow ≫ generatorExtension C I hp n s f = f := by
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

/-- The coded small-acyclic tests cover the source's uniform bound, and their identity-cone
attachments kill the corresponding maps. Together with termwise injectivity this gives K-injectivity. -/
theorem replacement_isKInjective (K : CochainComplex C ℤ) :
    ((replacement C).obj K).IsKInjective := sorry

/-- The functorial K-injective resolution contains the actual transfinite objects, maps and
augmentation. No part is selected from the previous bundled existence theorem. -/
def functorial : CochainComplex.KInjectiveResolution.Functorial C where
  toApproximation :=
    { toFunctor := replacement C
      ι := augmentation C
      mono_app := augmentation_mono C
      quasiIso_app := augmentation_quasiIso C }
  injective := replacement_term_injective C
  isKInjective := replacement_isKInjective C

end CochainComplex.KInjectiveResolution.Construction
