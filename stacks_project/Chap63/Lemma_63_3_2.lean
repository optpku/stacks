module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Subfunctor.Image
public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import stacks_project.Chap63.Lemma_63_3_1_ProperSupport

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [IsSeparated j]

/-- The pullback of the composite of an étale object over `U` with `j` back to `U`. -/
noncomputable abbrev diagonalPullback (V : U.Etale) : U.Etale :=
  (smallEtalePullback j).obj ((etaleRestriction j).obj V)

/-- The two legs defining the diagonal section satisfy the pullback relation. -/
theorem diagonalSection_condition (V : U.Etale) :
    𝟙 V.left ≫ ((etaleRestriction j).obj V).hom = V.hom ≫ j :=
  sorry

/-- The scheme map underlying the diagonal section into `V ×_X U`. -/
noncomputable def diagonalSectionHom (V : U.Etale) :
    V.left ⟶ (diagonalPullback j V).left :=
  pullback.lift (𝟙 V.left) V.hom (diagonalSection_condition j V)

/-- The diagonal section is a morphism over `U`. -/
theorem diagonalSectionHom_over (V : U.Etale) :
    diagonalSectionHom j V ≫ (diagonalPullback j V).hom = V.hom :=
  sorry

/-- The diagonal section, bundled in the small étale site of `U`. -/
noncomputable def diagonalSection (V : U.Etale) :
    V ⟶ diagonalPullback j V :=
  MorphismProperty.Over.homMk (diagonalSectionHom j V) (diagonalSectionHom_over j V)

/-- The diagonal section is an open immersion because the pullback projection is étale. -/
instance diagonalSectionHom_isOpenImmersion (V : U.Etale) :
    IsOpenImmersion (diagonalSectionHom j V) :=
  sorry

/-- The diagonal section is a closed immersion because `j` is separated. -/
instance diagonalSectionHom_isClosedImmersion (V : U.Etale) :
    IsClosedImmersion (diagonalSectionHom j V) :=
  sorry

/-- The open range of the diagonal section is also closed. -/
theorem diagonalRange_isClosed (V : U.Etale) :
    IsClosed ((diagonalSectionHom j V).opensRange : Set (diagonalPullback j V).left) :=
  sorry

/-- The open complement of the clopen diagonal section. -/
noncomputable def diagonalComplement (V : U.Etale) :
    (diagonalPullback j V).left.Opens :=
  ⟨((diagonalSectionHom j V).opensRange : Set (diagonalPullback j V).left)ᶜ,
    (diagonalRange_isClosed j V).isOpen_compl⟩

/-- The diagonal-range inclusion followed by the pullback structure map is étale. -/
instance diagonalRange_hom_etale (V : U.Etale) :
    Etale ((diagonalSectionHom j V).opensRange.ι ≫ (diagonalPullback j V).hom) :=
  sorry

/-- The complementary-open inclusion followed by the pullback structure map is étale. -/
instance diagonalComplement_hom_etale (V : U.Etale) :
    Etale ((diagonalComplement j V).ι ≫ (diagonalPullback j V).hom) :=
  sorry

/-- The diagonal range as an object of the small étale site of `U`. -/
noncomputable def diagonalRangeObject (V : U.Etale) : U.Etale :=
  MorphismProperty.Over.mk ⊤
    ((diagonalSectionHom j V).opensRange.ι ≫ (diagonalPullback j V).hom)
    (inferInstance : Etale
      ((diagonalSectionHom j V).opensRange.ι ≫ (diagonalPullback j V).hom))

/-- The complement of the diagonal range as an object of the small étale site of `U`. -/
noncomputable def diagonalComplementObject (V : U.Etale) : U.Etale :=
  MorphismProperty.Over.mk ⊤
    ((diagonalComplement j V).ι ≫ (diagonalPullback j V).hom)
    (inferInstance : Etale
      ((diagonalComplement j V).ι ≫ (diagonalPullback j V).hom))

/-- The diagonal-range inclusion respects the structure maps to `U`. -/
theorem diagonalRangeInclusion_over (V : U.Etale) :
    (diagonalSectionHom j V).opensRange.ι ≫ (diagonalPullback j V).hom =
      (diagonalRangeObject j V).hom :=
  sorry

/-- The complementary-open inclusion respects the structure maps to `U`. -/
theorem diagonalComplementInclusion_over (V : U.Etale) :
    (diagonalComplement j V).ι ≫ (diagonalPullback j V).hom =
      (diagonalComplementObject j V).hom :=
  sorry

/-- The inclusion of the diagonal range in the pullback object. -/
noncomputable def diagonalRangeInclusion (V : U.Etale) :
    diagonalRangeObject j V ⟶ diagonalPullback j V :=
  MorphismProperty.Over.homMk (diagonalSectionHom j V).opensRange.ι
    (diagonalRangeInclusion_over j V)

/-- The inclusion of the complementary open in the pullback object. -/
noncomputable def diagonalComplementInclusion (V : U.Etale) :
    diagonalComplementObject j V ⟶ diagonalPullback j V :=
  MorphismProperty.Over.homMk (diagonalComplement j V).ι
    (diagonalComplementInclusion_over j V)

/-- The canonical range isomorphism respects the structure maps to `U`. -/
theorem diagonalRangeIso_over (V : U.Etale) :
    (diagonalSectionHom j V).isoOpensRange.hom ≫ (diagonalRangeObject j V).hom = V.hom :=
  sorry

/-- The source of the diagonal section is canonically its open range, over `U`. -/
noncomputable def diagonalRangeIso (V : U.Etale) :
    V ≅ diagonalRangeObject j V :=
  MorphismProperty.Over.isoMk (diagonalSectionHom j V).isoOpensRange
    (diagonalRangeIso_over j V)

/-- The two members of the clopen cover by the diagonal range and its complement. -/
noncomputable def diagonalCoverObject (V : U.Etale) : Bool → U.Etale
  | false => diagonalRangeObject j V
  | true => diagonalComplementObject j V

/-- The two inclusions in the clopen cover by the diagonal range and its complement. -/
noncomputable def diagonalCoverMap (V : U.Etale) :
    ∀ i : Bool, diagonalCoverObject j V i ⟶ diagonalPullback j V
  | false => diagonalRangeInclusion j V
  | true => diagonalComplementInclusion j V

/-- The diagonal range and its complement cover the pullback object in the small étale
topology. -/
theorem diagonalCover_mem (V : U.Etale) :
    Sieve.ofArrows (diagonalCoverObject j V) (diagonalCoverMap j V) ∈
      U.smallEtaleTopology (diagonalPullback j V) :=
  sorry

/-- On the diagonal member use the original section; on the complement use zero. -/
noncomputable def diagonalExtensionLocalMap
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) (V : U.Etale) :
    ∀ i : Bool, F.obj.obj (op V) ⟶ F.obj.obj (op (diagonalCoverObject j V i))
  | false => F.obj.map (diagonalRangeIso j V).inv.op
  | true => 0

/-- The original section on the diagonal and zero on the complement agree on every overlap. -/
theorem diagonalExtensionLocalMap_compatible
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) (V : U.Etale) :
    ∀ (W : U.Etale) (i k : Bool) (a : W ⟶ diagonalCoverObject j V i)
      (b : W ⟶ diagonalCoverObject j V k),
      a ≫ diagonalCoverMap j V i = b ≫ diagonalCoverMap j V k →
        diagonalExtensionLocalMap j F V i ≫ F.obj.map a.op =
          diagonalExtensionLocalMap j F V k ≫ F.obj.map b.op :=
  sorry

/-- Extend a section on the diagonal range by zero on its open complement, using the
canonical amalgamation supplied by the sheaf condition. -/
noncomputable def diagonalExtensionMap
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) (V : U.Etale) :
    F.obj.obj (op V) ⟶ F.obj.obj (op (diagonalPullback j V)) :=
  F.property.amalgamateOfArrows (diagonalCoverMap j V) (diagonalCover_mem j V)
    (diagonalExtensionLocalMap j F V)
    (fun {W i k} a b h ↦ diagonalExtensionLocalMap_compatible j F V W i k a b h)

variable
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]

/-- The presheaf unit that extends a section by zero along the clopen diagonal. -/
noncomputable def abelianExtensionByZeroPresheafUnit
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    F.obj ⟶ (etaleRestriction j).op ⋙ (smallEtalePullback j).op ⋙ F.obj where
  app V := diagonalExtensionMap j F V.unop
  naturality := sorry

/-- The presheaf comparison induced by the clopen-diagonal extension maps. -/
noncomputable def abelianExtensionByZeroPresheafMap
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleRestriction j).op.leftKanExtension F.obj ⟶
      (smallEtalePullback j).op ⋙ F.obj :=
  (((etaleRestriction j).op.lanAdjunction AddCommGrpCat.{u}).homEquiv
    F.obj ((smallEtalePullback j).op ⋙ F.obj)).symm
      (abelianExtensionByZeroPresheafUnit j F)

/-- The sheaf-level component of the separated-étale comparison `j_! F ⟶ j_* F`. -/
noncomputable def abelianExtensionByZeroToDirectImageApp
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianExtensionByZero j).obj F ⟶ (etaleDirectImage j).obj F :=
  (sheafPullbackConstruction.sheafPullbackIso (etaleRestriction j) AddCommGrpCat.{u}
      U.smallEtaleTopology X.smallEtaleTopology).hom.app F ≫
    Sheaf.homEquiv.symm
      (sheafifyLift X.smallEtaleTopology (abelianExtensionByZeroPresheafMap j F)
        ((etaleDirectImage j).obj F).property)

/-- The concrete natural transformation comparing abelian extension by zero with
small étale direct image for a separated étale morphism. -/
noncomputable def abelianExtensionByZeroToDirectImage :
    abelianExtensionByZero j ⟶ etaleDirectImage j where
  app := abelianExtensionByZeroToDirectImageApp j
  naturality := sorry

variable (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})

/-- Lemma 63.3.2: if `j : U ⟶ X` is a separated étale morphism and `F` is an
abelian sheaf on `U_étale`, the image of the injective comparison
`j_! F ⟶ j_* F` from Étale Cohomology, Lemma 59.70.6 equals the proper-support
subsheaf of `j_* F` from Lemma 63.3.1. -/
@[stacks 0F4Y]
theorem abelianExtensionByZeroToDirectImage_range_eq :
    Subfunctor.range
      (Functor.whiskerRight ((abelianExtensionByZeroToDirectImage j).app F).hom
        (CategoryTheory.forget AddCommGrpCat)) =
      properSupportSubfunctor j F :=
  sorry

/-- A section of `j_* F` lies in the image of the comparison `j_! F ⟶ j_* F` if
and only if it has proper support over the base. -/
theorem mem_range_abelianExtensionByZeroToDirectImage_iff
    (V : X.Etale) (σ : ((etaleDirectImage j).obj F).obj.obj (op V)) :
    (∃ τ, ((abelianExtensionByZeroToDirectImage j).app F).hom.app (op V) τ = σ) ↔
      HasProperSupportOver j F V σ :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
