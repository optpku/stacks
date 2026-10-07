module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InverseImage

/-!
# Inverse image of relative de Rham complexes

The comparison is stated on arbitrary ringed sites.  Topological-space and ringed-space versions
are direct specializations of this owner.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DeRham

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [K.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasWeakSheafify K CommRingCat.{max u v}]
variable [HasWeakSheafify K AddCommGrpCat.{max u v}]
variable [K.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ P : Cᵒᵖ ⥤ CommRingCat.{max u v}, F.op.HasLeftKanExtension P]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}
variable [(SheafOfModules.pushforward
  (InverseImage.structureMap (J := J) (K := K) F O₁)).IsRightAdjoint]

/-- The inverse-image morphism of commutative ring sheaves. -/
abbrev inverseImageMap (φ : O₁ ⟶ O₂) :
    (InverseImage.ringPullback (J := J) (K := K) F).obj O₁ ⟶
      (InverseImage.ringPullback (J := J) (K := K) F).obj O₂ :=
  (InverseImage.ringPullback (J := J) (K := K) F).map φ

/-- The degree-`p` target of the inverse-image comparison. -/
abbrev inverseImageTerm (φ : O₁ ⟶ O₂) (p : ℕ) :=
  term (inverseImageMap (J := J) (K := K) F φ) p

/-- The degree-`p` target term pushed back to the source site. -/
abbrev pushedInverseImageTerm (φ : O₁ ⟶ O₂) (p : ℕ) :=
  (SheafOfModules.pushforward
    (InverseImage.structureMap (J := J) (K := K) F O₁)).obj
      (inverseImageTerm (J := J) (K := K) F φ p)

/-- On every object of the source site, the two inverse-image adjunction units form a
commutative square with the original and pulled-back ring maps. -/
theorem unitSquareApp (φ : O₁ ⟶ O₂) (U : Cᵒᵖ) :
    CommSq
      (((F.sheafAdjunctionContinuous CommRingCat.{max u v} J K).unit.app O₁).hom.app U)
      (φ.hom.app U)
      ((inverseImageMap (J := J) (K := K) F φ).hom.app (F.op.obj U))
      (((F.sheafAdjunctionContinuous CommRingCat.{max u v} J K).unit.app O₂).hom.app U) := sorry

/-- The sectionwise degree-`p` map underlying inverse-image comparison of de Rham terms. -/
noncomputable def comparisonPresheafApp (φ : O₁ ⟶ O₂) (p : ℕ) (U : Cᵒᵖ) :
    (PresheafOfModules.DeRham.term φ.hom p).obj U ⟶
      (pushedInverseImageTerm (J := J) (K := K) F φ p).val.obj U :=
  CommRingCat.DeRham.mapApp (unitSquareApp (J := J) (K := K) F φ U) p ≫
    (ModuleCat.restrictScalars
      (((F.sheafAdjunctionContinuous CommRingCat.{max u v} J K).unit.app O₁).hom.app U).hom).map
      (((termUnit (inverseImageMap (J := J) (K := K) F φ) p).app (F.op.obj U)) ≫
        (valRestrictionIso
          ((InverseImage.ringPullback (J := J) (K := K) F).obj O₁)
          (inverseImageTerm (J := J) (K := K) F φ p)).inv.app (F.op.obj U))

/-- The sectionwise inverse-image comparison sends a basic form to the basic form obtained by
applying the inverse-image unit to every entry. -/
theorem comparisonPresheafApp_basic (φ : O₁ ⟶ O₂) (p : ℕ) (U : Cᵒᵖ)
    (b₀ : O₂.obj.obj U) (bs : Fin p → O₂.obj.obj U) :
    comparisonPresheafApp (J := J) (K := K) F φ p U
        (PresheafOfModules.DeRham.termBasic φ.hom p U b₀ bs) =
      basic (inverseImageMap (J := J) (K := K) F φ) p (F.op.obj U)
        (((F.sheafAdjunctionContinuous CommRingCat.{max u v} J K).unit.app O₂).hom.app U b₀)
        (fun i ↦
          ((F.sheafAdjunctionContinuous CommRingCat.{max u v} J K).unit.app O₂).hom.app U
            (bs i)) := sorry

/-- The sectionwise inverse-image comparison commutes with restriction maps. -/
theorem comparisonPresheafApp_naturality (φ : O₁ ⟶ O₂) (p : ℕ)
    {U V : Cᵒᵖ} (i : U ⟶ V) :
    (PresheafOfModules.DeRham.term φ.hom p).map i ≫
        (ModuleCat.restrictScalars (((ringSheaf J O₁).obj.map i).hom)).map
          (comparisonPresheafApp (J := J) (K := K) F φ p V) =
      comparisonPresheafApp (J := J) (K := K) F φ p U ≫
        (pushedInverseImageTerm (J := J) (K := K) F φ p).val.map i := sorry

/-- The morphism of module presheaves underlying degreewise inverse-image comparison. -/
noncomputable def comparisonPresheaf (φ : O₁ ⟶ O₂) (p : ℕ) :
    PresheafOfModules.DeRham.term φ.hom p ⟶
      (pushedInverseImageTerm (J := J) (K := K) F φ p).val where
  app U := comparisonPresheafApp (J := J) (K := K) F φ p U
  naturality i := comparisonPresheafApp_naturality (J := J) (K := K) F φ p i

/-- The adjoint-side degreewise comparison, from the original de Rham term to the pushforward of
the pulled-back term. -/
noncomputable def comparisonAdjoint (φ : O₁ ⟶ O₂) (p : ℕ) :
    term φ p ⟶ pushedInverseImageTerm (J := J) (K := K) F φ p :=
  (ModuleSheafification.restrictionComponentIso φ
      (PresheafOfModules.DeRham.form φ.hom p)).inv ≫
    ((moduleSheafificationAdjunction O₁).homEquiv _ _).symm
      (comparisonPresheaf (J := J) (K := K) F φ p ≫
        (valRestrictionIso O₁
          (pushedInverseImageTerm (J := J) (K := K) F φ p)).hom)

/-- The canonical degreewise comparison from the inverse image of a relative de Rham term to the
corresponding term of the pulled-back ring map. -/
@[stacks 0FKP "degreewise comparison morphism"]
noncomputable def comparisonApp (φ : O₁ ⟶ O₂) (p : ℕ) :
    (InverseImage.modulePullback (J := J) (K := K) F O₁).obj (term φ p) ⟶
      inverseImageTerm (J := J) (K := K) F φ p :=
  ((SheafOfModules.pullbackPushforwardAdjunction
    (InverseImage.structureMap (J := J) (K := K) F O₁)).homEquiv _ _).symm
      (comparisonAdjoint (J := J) (K := K) F φ p)

/-- Transposing the degreewise inverse-image comparison recovers its explicit adjoint-side map. -/
@[simp]
theorem comparisonApp_adj (φ : O₁ ⟶ O₂) (p : ℕ) :
    (SheafOfModules.pullbackPushforwardAdjunction
      (InverseImage.structureMap (J := J) (K := K) F O₁)).homEquiv _ _
        (comparisonApp (J := J) (K := K) F φ p) =
      comparisonAdjoint (J := J) (K := K) F φ p := sorry

/- The degreewise comparison is the one place where the current construction still needs an
invertibility gate before the literal Iso can be assembled.  The named inverse below records the
resulting categorical choice as a reusable owner. -/
/-- The degreewise inverse-image comparison is an isomorphism. -/
@[stacks 0FKP "degreewise comparison invertibility gate"]
instance comparisonApp_isIso (φ : O₁ ⟶ O₂) (p : ℕ) :
    IsIso (comparisonApp (J := J) (K := K) F φ p) := sorry

/-- The named inverse of the degreewise inverse-image comparison.  Downstream constructions should
use this owner instead of selecting `CategoryTheory.inv` at each use site. -/
@[stacks 0FKP "degreewise inverse comparison"]
noncomputable def comparisonAppInv (φ : O₁ ⟶ O₂) (p : ℕ) :
    inverseImageTerm (J := J) (K := K) F φ p ⟶
      (InverseImage.modulePullback (J := J) (K := K) F O₁).obj (term φ p) :=
  inv (comparisonApp (J := J) (K := K) F φ p)

/-- The degreewise comparison followed by its named inverse is the identity. -/
@[simp, stacks 0FKP "degreewise forward-inverse comparison law"]
theorem comparisonApp_hom_inv_id (φ : O₁ ⟶ O₂) (p : ℕ) :
    comparisonApp (J := J) (K := K) F φ p ≫
        comparisonAppInv (J := J) (K := K) F φ p = 𝟙 _ := sorry

/-- The named degreewise inverse followed by the comparison is the identity. -/
@[simp, stacks 0FKP "degreewise inverse-forward comparison law"]
theorem comparisonApp_inv_hom_id (φ : O₁ ⟶ O₂) (p : ℕ) :
    comparisonAppInv (J := J) (K := K) F φ p ≫
        comparisonApp (J := J) (K := K) F φ p = 𝟙 _ := sorry

/-- The canonical degreewise inverse-image comparison as an isomorphism. -/
@[stacks 0FKP "degreewise comparison isomorphism"]
noncomputable def comparisonAppIso (φ : O₁ ⟶ O₂) (p : ℕ) :
    (InverseImage.modulePullback (J := J) (K := K) F O₁).obj (term φ p) ≅
      inverseImageTerm (J := J) (K := K) F φ p :=
  { hom := comparisonApp (J := J) (K := K) F φ p
    inv := comparisonAppInv (J := J) (K := K) F φ p
    hom_inv_id := comparisonApp_hom_inv_id (J := J) (K := K) F φ p
    inv_hom_id := comparisonApp_inv_hom_id (J := J) (K := K) F φ p }

/-- The forward map of the degreewise comparison isomorphism is `comparisonApp`. -/
@[simp, stacks 0FKP "degreewise comparison isomorphism hom"]
theorem comparisonAppIso_hom (φ : O₁ ⟶ O₂) (p : ℕ) :
    (comparisonAppIso (J := J) (K := K) F φ p).hom =
      comparisonApp (J := J) (K := K) F φ p := sorry

/-- The inverse component of the degreewise comparison is the named map `comparisonAppInv`. -/
@[simp, stacks 0FKP "degreewise comparison isomorphism inv"]
theorem comparisonAppIso_inv (φ : O₁ ⟶ O₂) (p : ℕ) :
    (comparisonAppIso (J := J) (K := K) F φ p).inv =
      comparisonAppInv (J := J) (K := K) F φ p := sorry

/-- The degreewise comparison maps commute with all de Rham differentials. -/
theorem comparisonApp_comm (φ : O₁ ⟶ O₂) (i j : ℕ)
    (hij : (up ℕ).Rel i j) :
    comparisonApp (J := J) (K := K) F φ i ≫
        (complex (inverseImageMap (J := J) (K := K) F φ)).d i j =
      (((InverseImage.modulePullback (J := J) (K := K) F O₁).mapHomologicalComplex
        (up ℕ)).obj (complex φ)).d i j ≫
        comparisonApp (J := J) (K := K) F φ j := sorry

/-- The degreewise comparison isomorphisms commute with all de Rham differentials. -/
@[stacks 0FKP "degreewise comparison isomorphism compatibility"]
theorem comparisonAppIso_comm (φ : O₁ ⟶ O₂) (i j : ℕ)
    (hij : (up ℕ).Rel i j) :
    (comparisonAppIso (J := J) (K := K) F φ i).hom ≫
        (complex (inverseImageMap (J := J) (K := K) F φ)).d i j =
      (((InverseImage.modulePullback (J := J) (K := K) F O₁).mapHomologicalComplex
        (up ℕ)).obj (complex φ)).d i j ≫
        (comparisonAppIso (J := J) (K := K) F φ j).hom := sorry

/-- The named inverses of the degreewise comparisons commute with all de Rham differentials. -/
@[stacks 0FKP "degreewise inverse comparison compatibility"]
theorem comparisonAppIso_inv_comm (φ : O₁ ⟶ O₂) (i j : ℕ)
    (hij : (up ℕ).Rel i j) :
    comparisonAppInv (J := J) (K := K) F φ i ≫
        (((InverseImage.modulePullback (J := J) (K := K) F O₁).mapHomologicalComplex
          (up ℕ)).obj (complex φ)).d i j =
      (complex (inverseImageMap (J := J) (K := K) F φ)).d i j ≫
        comparisonAppInv (J := J) (K := K) F φ j := sorry

/-- Lemma 17.30.2 (0FKP): the canonical inverse-image identification of relative de Rham
complexes. -/
@[stacks 0FKP "canonical inverse-image identification"]
noncomputable def comparisonIso (φ : O₁ ⟶ O₂) :
    ((InverseImage.modulePullback
      (J := J) (K := K) F O₁).mapHomologicalComplex (up ℕ)).obj (complex φ) ≅
        complex (inverseImageMap (J := J) (K := K) F φ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ comparisonAppIso (J := J) (K := K) F φ p)
    (fun i j hij ↦ comparisonAppIso_comm (J := J) (K := K) F φ i j hij)

/-- Lemma 17.30.2 (0FKP): the explicit comparison from the inverse image of a relative de Rham
complex to the relative de Rham complex of the pulled-back ring map.  It is the forward map of
the componentwise literal isomorphism. -/
@[stacks 0FKP "comparison morphism"]
noncomputable abbrev comparison (φ : O₁ ⟶ O₂) :
    ((InverseImage.modulePullback
      (J := J) (K := K) F O₁).mapHomologicalComplex (up ℕ)).obj (complex φ) ⟶
        complex (inverseImageMap (J := J) (K := K) F φ) :=
  (comparisonIso (J := J) (K := K) F φ).hom

/-- The forward map of `comparisonIso` is the canonical comparison. -/
@[simp, stacks 0FKP "comparison isomorphism hom"]
theorem comparisonIso_hom (φ : O₁ ⟶ O₂) :
    (comparisonIso (J := J) (K := K) F φ).hom =
      comparison (J := J) (K := K) F φ := sorry

/-- The degree-`p` component of the inverse-image comparison is `comparisonApp`. -/
@[stacks 0FKP "comparison component"]
theorem comparison_f (φ : O₁ ⟶ O₂) (p : ℕ) :
    (comparison (J := J) (K := K) F φ).f p =
      comparisonApp (J := J) (K := K) F φ p := sorry

/-- The canonical comparison is invertible.  Typeclass search also obtains this directly by
unfolding `comparison` and applying `Iso.isIso_hom`. -/
@[stacks 0FKP "comparison is an isomorphism"]
theorem comparison_isIso (φ : O₁ ⟶ O₂) :
    IsIso (comparison (J := J) (K := K) F φ) := sorry

/-- The inverse morphism owned by the relative de Rham inverse-image comparison. -/
@[stacks 0FKP "inverse comparison morphism"]
noncomputable def comparisonInv (φ : O₁ ⟶ O₂) :
    complex (inverseImageMap (J := J) (K := K) F φ) ⟶
      ((InverseImage.modulePullback
        (J := J) (K := K) F O₁).mapHomologicalComplex (up ℕ)).obj (complex φ) :=
  (comparisonIso (J := J) (K := K) F φ).inv

/-- The inverse map of `comparisonIso` is the named `comparisonInv`. -/
@[simp, stacks 0FKP "comparison isomorphism inv"]
theorem comparisonIso_inv (φ : O₁ ⟶ O₂) :
    (comparisonIso (J := J) (K := K) F φ).inv =
      comparisonInv (J := J) (K := K) F φ := sorry

/-- The degree-`p` forward component of `comparisonIso` is `comparisonApp`. -/
@[simp, stacks 0FKP "comparison isomorphism component"]
theorem comparisonIso_hom_f (φ : O₁ ⟶ O₂) (p : ℕ) :
    (comparisonIso (J := J) (K := K) F φ).hom.f p =
      comparisonApp (J := J) (K := K) F φ p := sorry

/-- The degree-`p` inverse component of `comparisonIso` is the named `comparisonAppInv`. -/
@[simp, stacks 0FKP "inverse comparison component"]
theorem comparisonIso_inv_f (φ : O₁ ⟶ O₂) (p : ℕ) :
    (comparisonIso (J := J) (K := K) F φ).inv.f p =
      comparisonAppInv (J := J) (K := K) F φ p := sorry

/-- The de Rham comparison followed by its named inverse is the identity. -/
@[simp, stacks 0FKP "forward-inverse comparison law"]
theorem comparison_hom_inv_id (φ : O₁ ⟶ O₂) :
    comparison (J := J) (K := K) F φ ≫
        comparisonInv (J := J) (K := K) F φ = 𝟙 _ := sorry

/-- The named de Rham inverse followed by the comparison is the identity. -/
@[simp, stacks 0FKP "inverse-forward comparison law"]
theorem comparison_inv_hom_id (φ : O₁ ⟶ O₂) :
    comparisonInv (J := J) (K := K) F φ ≫
        comparison (J := J) (K := K) F φ = 𝟙 _ := sorry

/-- Inverse image identifies each scalar-restricted relative de Rham term with the corresponding
term for the pulled-back ring-sheaf morphism. -/
theorem inverseImage_term_isIsomorphic (φ : O₁ ⟶ O₂) (p : ℕ) :
    IsIsomorphic
      ((InverseImage.modulePullback (J := J) (K := K) F O₁).obj (term φ p))
      (term ((InverseImage.ringPullback (J := J) (K := K) F).map φ) p) := sorry

/-- Lemma 17.30.2 (0FKP): inverse image preserves the relative de Rham complex of a morphism of
commutative ring sheaves. -/
@[stacks 0FKP]
theorem inverseImage_isIsomorphic (φ : O₁ ⟶ O₂) :
    IsIsomorphic
      (((InverseImage.modulePullback
          (J := J) (K := K) F O₁).mapHomologicalComplex (up ℕ)).obj (complex φ))
      (complex ((InverseImage.ringPullback (J := J) (K := K) F).map φ)) := sorry

end SheafOfModules.RingedSite.DeRham

-- The component inverse still uses the categorical inverse selected by
-- `comparisonApp_isIso`, so it inherits that gate's current proof debt.  The complex-level
-- comparison and inverse are instead the hom and inv of the componentwise literal Iso; no
-- second `IsIso` instance or categorical inverse is selected at the complex level.
