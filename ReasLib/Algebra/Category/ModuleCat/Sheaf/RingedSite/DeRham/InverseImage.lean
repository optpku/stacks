module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InverseImage
public import Mathlib.CategoryTheory.Functor.Flat

/-!
# Inverse image of relative de Rham complexes

The forward comparison is stated for every continuous functor of sites.  Its inverse side requires
representable flatness, which holds for the open-preimage functor of a continuous map.
Topological-space and ringed-space versions are direct specializations of this owner.
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

/-- The degreewise comparison maps commute with all de Rham differentials. -/
theorem comparisonApp_comm (φ : O₁ ⟶ O₂) (i j : ℕ)
    (hij : (up ℕ).Rel i j) :
    comparisonApp (J := J) (K := K) F φ i ≫
        (complex (inverseImageMap (J := J) (K := K) F φ)).d i j =
      (((InverseImage.modulePullback (J := J) (K := K) F O₁).mapHomologicalComplex
        (up ℕ)).obj (complex φ)).d i j ≫
        comparisonApp (J := J) (K := K) F φ j := sorry

/-- Lemma 17.30.2 (0FKP): the explicit comparison from the inverse image of a relative de Rham
complex to the relative de Rham complex of the pulled-back ring map, assembled from the
degreewise comparisons.  It exists for every continuous functor of sites. -/
@[stacks 0FKP "comparison morphism"]
noncomputable def comparison (φ : O₁ ⟶ O₂) :
    ((InverseImage.modulePullback
      (J := J) (K := K) F O₁).mapHomologicalComplex (up ℕ)).obj (complex φ) ⟶
        complex (inverseImageMap (J := J) (K := K) F φ) where
  f p := comparisonApp (J := J) (K := K) F φ p
  comm' i j hij := comparisonApp_comm (J := J) (K := K) F φ i j hij

/-- The degree-`p` component of the inverse-image comparison is `comparisonApp`. -/
@[simp, stacks 0FKP "comparison component"]
theorem comparison_f (φ : O₁ ⟶ O₂) (p : ℕ) :
    (comparison (J := J) (K := K) F φ).f p =
      comparisonApp (J := J) (K := K) F φ p := rfl

/-!
## Invertibility under representable flatness

The source works with a continuous map of topological spaces, whose open-preimage functor is
representably flat (`Opens.map f` has a mathlib `RepresentablyFlat` instance).  Flatness is needed:
for an arbitrary continuous functor, inverse image of commutative ring sheaves is a colimit in
`CommRingCat` over a possibly non-filtered index category, and already in degree `0` it differs
from inverse image of the underlying module.  For the trivial topologies, a one-object `D`, and a
two-object discrete `C` mapped to it, with constant `O₁ = 𝔽₂` and `O₂ = 𝔽₂³`, the pulled-back
ring has dimension `9` while the pulled-back module has dimension `6`.

The degreewise inverse below is still the categorical inverse selected from the admitted
invertibility gate `comparisonApp_isIso`.  An explicit reverse map needs the reverse
(lax) multiplicative structure of flat module pullback and the commutation of module pullback with
restriction of scalars; these prerequisites are tracked separately in the lib-int ledger.
-/

variable [RepresentablyFlat F]

/-- For a representably flat continuous functor, the degreewise inverse-image comparison is an
isomorphism. -/
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
      inverseImageTerm (J := J) (K := K) F φ p where
  hom := comparisonApp (J := J) (K := K) F φ p
  inv := comparisonAppInv (J := J) (K := K) F φ p
  hom_inv_id := comparisonApp_hom_inv_id (J := J) (K := K) F φ p
  inv_hom_id := comparisonApp_inv_hom_id (J := J) (K := K) F φ p

/-- The forward map of the degreewise comparison isomorphism is `comparisonApp`. -/
@[simp, stacks 0FKP "degreewise comparison isomorphism hom"]
theorem comparisonAppIso_hom (φ : O₁ ⟶ O₂) (p : ℕ) :
    (comparisonAppIso (J := J) (K := K) F φ p).hom =
      comparisonApp (J := J) (K := K) F φ p := rfl

/-- The inverse component of the degreewise comparison is the named map `comparisonAppInv`. -/
@[simp, stacks 0FKP "degreewise comparison isomorphism inv"]
theorem comparisonAppIso_inv (φ : O₁ ⟶ O₂) (p : ℕ) :
    (comparisonAppIso (J := J) (K := K) F φ p).inv =
      comparisonAppInv (J := J) (K := K) F φ p := rfl

/-- The degreewise comparison isomorphisms commute with all de Rham differentials. -/
@[stacks 0FKP "degreewise comparison isomorphism compatibility"]
theorem comparisonAppIso_comm (φ : O₁ ⟶ O₂) (i j : ℕ)
    (hij : (up ℕ).Rel i j) :
    (comparisonAppIso (J := J) (K := K) F φ i).hom ≫
        (complex (inverseImageMap (J := J) (K := K) F φ)).d i j =
      (((InverseImage.modulePullback (J := J) (K := K) F O₁).mapHomologicalComplex
        (up ℕ)).obj (complex φ)).d i j ≫
        (comparisonAppIso (J := J) (K := K) F φ j).hom :=
  comparisonApp_comm (J := J) (K := K) F φ i j hij

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
complexes along a representably flat continuous functor. -/
@[stacks 0FKP "canonical inverse-image identification"]
noncomputable def comparisonIso (φ : O₁ ⟶ O₂) :
    ((InverseImage.modulePullback
      (J := J) (K := K) F O₁).mapHomologicalComplex (up ℕ)).obj (complex φ) ≅
        complex (inverseImageMap (J := J) (K := K) F φ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ comparisonAppIso (J := J) (K := K) F φ p)
    (fun i j hij ↦ comparisonAppIso_comm (J := J) (K := K) F φ i j hij)

/-- The forward map of `comparisonIso` is the canonical comparison. -/
@[simp, stacks 0FKP "comparison isomorphism hom"]
theorem comparisonIso_hom (φ : O₁ ⟶ O₂) :
    (comparisonIso (J := J) (K := K) F φ).hom =
      comparison (J := J) (K := K) F φ := sorry

/-- The canonical comparison along a representably flat continuous functor is invertible. -/
@[stacks 0FKP "comparison is an isomorphism"]
instance comparison_isIso (φ : O₁ ⟶ O₂) :
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
      comparisonInv (J := J) (K := K) F φ := rfl

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

/-- Inverse image along a representably flat continuous functor identifies each
scalar-restricted relative de Rham term with the corresponding term for the pulled-back
ring-sheaf morphism. -/
theorem inverseImage_term_isIsomorphic (φ : O₁ ⟶ O₂) (p : ℕ) :
    IsIsomorphic
      ((InverseImage.modulePullback (J := J) (K := K) F O₁).obj (term φ p))
      (term ((InverseImage.ringPullback (J := J) (K := K) F).map φ) p) := sorry

/-- Lemma 17.30.2 (0FKP): inverse image along a representably flat continuous functor preserves
the relative de Rham complex of a morphism of commutative ring sheaves. -/
@[stacks 0FKP]
theorem inverseImage_isIsomorphic (φ : O₁ ⟶ O₂) :
    IsIsomorphic
      (((InverseImage.modulePullback
          (J := J) (K := K) F O₁).mapHomologicalComplex (up ℕ)).obj (complex φ))
      (complex ((InverseImage.ringPullback (J := J) (K := K) F).map φ)) := sorry

end SheafOfModules.RingedSite.DeRham
