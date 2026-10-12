/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open Opposite

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme
namespace ExtensionByZeroComparison

variable {U X : Scheme.{u}}
variable (j : U ⟶ X) [Etale j] [IsSeparated j]

/-- The pullback of the composite of an étale object over `U` with `j` back to `U`. -/
noncomputable abbrev diagonalPullback (V : U.Etale) : U.Etale :=
  (smallEtalePullback j).obj ((etaleRestriction j).obj V)

/-- The two legs defining the diagonal section satisfy the pullback relation. -/
theorem diagonalSection_condition (V : U.Etale) :
    𝟙 V.left ≫ ((etaleRestriction j).obj V).hom = V.hom ≫ j := sorry

/-- The scheme map underlying the diagonal section into `V ×_X U`. -/
noncomputable def diagonalSectionHom (V : U.Etale) :
    V.left ⟶ (diagonalPullback j V).left :=
  pullback.lift (𝟙 V.left) V.hom (diagonalSection_condition j V)

/-- The diagonal section is a morphism over `U`. -/
theorem diagonalSectionHom_over (V : U.Etale) :
    diagonalSectionHom j V ≫ (diagonalPullback j V).hom = V.hom := sorry

/-- The diagonal section, bundled in the small étale site of `U`. -/
noncomputable def diagonalSection (V : U.Etale) :
    V ⟶ diagonalPullback j V :=
  MorphismProperty.Over.homMk (diagonalSectionHom j V)
    (diagonalSectionHom_over j V)

/-- The diagonal section is an open immersion because the pullback projection is étale. -/
instance diagonalSectionHom_isOpenImmersion (V : U.Etale) :
    IsOpenImmersion (diagonalSectionHom j V) := sorry

/-- The diagonal section is a closed immersion because `j` is separated. -/
instance diagonalSectionHom_isClosedImmersion (V : U.Etale) :
    IsClosedImmersion (diagonalSectionHom j V) := sorry

/-- The open range of the diagonal section is also closed. -/
theorem diagonalRange_isClosed (V : U.Etale) :
    IsClosed ((diagonalSectionHom j V).opensRange : Set (diagonalPullback j V).left) := sorry

/-- The open complement of the clopen diagonal section. -/
noncomputable def diagonalComplement (V : U.Etale) :
    (diagonalPullback j V).left.Opens :=
  ⟨((diagonalSectionHom j V).opensRange : Set (diagonalPullback j V).left)ᶜ,
    (diagonalRange_isClosed j V).isOpen_compl⟩

/-- The diagonal-range inclusion followed by the pullback structure map is étale. -/
instance diagonalRange_hom_etale (V : U.Etale) :
    Etale ((diagonalSectionHom j V).opensRange.ι ≫ (diagonalPullback j V).hom) := sorry

/-- The complementary-open inclusion followed by the pullback structure map is étale. -/
instance diagonalComplement_hom_etale (V : U.Etale) :
    Etale ((diagonalComplement j V).ι ≫ (diagonalPullback j V).hom) := sorry

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
      (diagonalRangeObject j V).hom := sorry

/-- The complementary-open inclusion respects the structure maps to `U`. -/
theorem diagonalComplementInclusion_over (V : U.Etale) :
    (diagonalComplement j V).ι ≫ (diagonalPullback j V).hom =
      (diagonalComplementObject j V).hom := sorry

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
    (diagonalSectionHom j V).isoOpensRange.hom ≫ (diagonalRangeObject j V).hom =
      V.hom := sorry

/-- The source of the diagonal section is canonically its open range, over `U`. -/
noncomputable def diagonalRangeIso (V : U.Etale) :
    V ≅ diagonalRangeObject j V :=
  MorphismProperty.Over.isoMk (diagonalSectionHom j V).isoOpensRange
    (diagonalRangeIso_over j V)

variable (A : Type (w + 1)) [Category.{w} A] [HasZeroMorphisms A]

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
      U.smallEtaleTopology (diagonalPullback j V) := sorry

/-- On the diagonal member use the original section; on the complement use zero. -/
noncomputable def diagonalExtensionLocalMap
    (F : Sheaf U.smallEtaleTopology A) (V : U.Etale) :
    ∀ i : Bool, F.obj.obj (op V) ⟶ F.obj.obj (op (diagonalCoverObject j V i))
  | false => F.obj.map (diagonalRangeIso j V).inv.op
  | true => 0

/-- The original section on the diagonal and zero on the complement agree on every overlap. -/
theorem diagonalExtensionLocalMap_compatible
    (F : Sheaf U.smallEtaleTopology A) (V : U.Etale) :
    ∀ (W : U.Etale) (i k : Bool)
      (a : W ⟶ diagonalCoverObject j V i)
      (b : W ⟶ diagonalCoverObject j V k),
      a ≫ diagonalCoverMap j V i = b ≫ diagonalCoverMap j V k →
        diagonalExtensionLocalMap j A F V i ≫ F.obj.map a.op =
          diagonalExtensionLocalMap j A F V k ≫ F.obj.map b.op := sorry

/-- Extend a section on the diagonal range by zero on its open complement, using the
canonical amalgamation supplied by the sheaf condition. -/
noncomputable def diagonalExtensionMap
    (F : Sheaf U.smallEtaleTopology A) (V : U.Etale) :
    F.obj.obj (op V) ⟶ F.obj.obj (op (diagonalPullback j V)) :=
  F.property.amalgamateOfArrows (diagonalCoverMap j V) (diagonalCover_mem j V)
    (diagonalExtensionLocalMap j A F V)
    (fun {W i k} a b h ↦
      diagonalExtensionLocalMap_compatible j A F V W i k a b h)

/-- Restricting the diagonal extension back to the diagonal range recovers the original
section through the canonical range isomorphism. -/
theorem diagonalExtensionMap_range
    (F : Sheaf U.smallEtaleTopology A) (V : U.Etale) :
    diagonalExtensionMap j A F V ≫ F.obj.map (diagonalRangeInclusion j V).op =
      F.obj.map (diagonalRangeIso j V).inv.op := sorry

/-- Restricting the diagonal extension to the complementary open is zero. -/
theorem diagonalExtensionMap_complement
    (F : Sheaf U.smallEtaleTopology A) (V : U.Etale) :
    diagonalExtensionMap j A F V ≫ F.obj.map (diagonalComplementInclusion j V).op = 0 := sorry

end ExtensionByZeroComparison

open ExtensionByZeroComparison

variable {U X : Scheme.{u}}
variable (j : U ⟶ X) [Etale j] [IsSeparated j]

variable
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]

/-- The presheaf unit that extends a section by zero along the clopen diagonal. -/
noncomputable def abelianExtensionByZeroPresheafUnit
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{w}) :
    F.obj ⟶ (etaleRestriction j).op ⋙ (smallEtalePullback j).op ⋙ F.obj where
  app V := diagonalExtensionMap j AddCommGrpCat.{w} F V.unop
  naturality := sorry

/-- The presheaf comparison induced by the clopen-diagonal extension maps. -/
noncomputable def abelianExtensionByZeroPresheafMap
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{w}) :
    (etaleRestriction j).op.leftKanExtension F.obj ⟶
      (smallEtalePullback j).op ⋙ F.obj :=
  (((etaleRestriction j).op.lanAdjunction AddCommGrpCat.{w}).homEquiv
    F.obj ((smallEtalePullback j).op ⋙ F.obj)).symm
      (abelianExtensionByZeroPresheafUnit j F)

/-- The sheaf-level component of the separated-étale comparison. -/
noncomputable def abelianExtensionByZeroToDirectImageApp
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{w}) :
    (abelianExtensionByZero j).obj F ⟶
      ((smallEtalePullback j).sheafPushforwardContinuous
        AddCommGrpCat.{w} X.smallEtaleTopology U.smallEtaleTopology).obj F :=
  (sheafPullbackConstruction.sheafPullbackIso (etaleRestriction j)
      AddCommGrpCat.{w} U.smallEtaleTopology X.smallEtaleTopology).hom.app F ≫
    Sheaf.homEquiv.symm
      (sheafifyLift X.smallEtaleTopology
        (abelianExtensionByZeroPresheafMap j F)
        (((smallEtalePullback j).sheafPushforwardContinuous
          AddCommGrpCat.{w} X.smallEtaleTopology U.smallEtaleTopology).obj F).property)

/-- The concrete natural transformation comparing abelian extension by zero with
small étale direct image for a separated étale morphism. -/
noncomputable def abelianExtensionByZeroToDirectImage :
    abelianExtensionByZero j ⟶
      (smallEtalePullback j).sheafPushforwardContinuous
        AddCommGrpCat.{w} X.smallEtaleTopology U.smallEtaleTopology where
  app := abelianExtensionByZeroToDirectImageApp j
  naturality := sorry

variable {Λ : Type w} [Ring Λ]

variable
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]

/-- The module-presheaf unit that extends a section by zero along the clopen diagonal. -/
noncomputable def moduleExtensionByZeroPresheafUnit
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ)) :
    F.obj ⟶ (etaleRestriction j).op ⋙ (smallEtalePullback j).op ⋙ F.obj where
  app V := diagonalExtensionMap j (ModuleCat.{w} Λ) F V.unop
  naturality := sorry

/-- The module-presheaf comparison induced by the clopen-diagonal extension maps. -/
noncomputable def moduleExtensionByZeroPresheafMap
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ)) :
    (etaleRestriction j).op.leftKanExtension F.obj ⟶
      (smallEtalePullback j).op ⋙ F.obj :=
  (((etaleRestriction j).op.lanAdjunction (ModuleCat.{w} Λ)).homEquiv
    F.obj ((smallEtalePullback j).op ⋙ F.obj)).symm
      (moduleExtensionByZeroPresheafUnit j F)

/-- The sheaf-level module component of the separated-étale comparison. -/
noncomputable def moduleExtensionByZeroToDirectImageApp
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ)) :
    (moduleExtensionByZero j).obj F ⟶
      ((smallEtalePullback j).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) X.smallEtaleTopology U.smallEtaleTopology).obj F :=
  (sheafPullbackConstruction.sheafPullbackIso (etaleRestriction j)
      (ModuleCat.{w} Λ) U.smallEtaleTopology X.smallEtaleTopology).hom.app F ≫
    Sheaf.homEquiv.symm
      (sheafifyLift X.smallEtaleTopology
        (moduleExtensionByZeroPresheafMap j F)
        (((smallEtalePullback j).sheafPushforwardContinuous
          (ModuleCat.{w} Λ) X.smallEtaleTopology U.smallEtaleTopology).obj F).property)

/-- The concrete natural transformation comparing module extension by zero with
small étale direct image for a separated étale morphism. -/
noncomputable def moduleExtensionByZeroToDirectImage :
    moduleExtensionByZero j ⟶
      (smallEtalePullback j).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) X.smallEtaleTopology U.smallEtaleTopology where
  app := moduleExtensionByZeroToDirectImageApp j
  naturality := sorry

section AbelianMono

variable {U X : Scheme.{u}}
variable (j : U ⟶ X) [Etale j] [IsSeparated j]

variable
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]

/-- Each component of the abelian extension-by-zero comparison is a monomorphism. -/
instance abelianExtensionByZeroToDirectImage_app_mono
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{w}) :
    Mono ((abelianExtensionByZeroToDirectImage j).app F) := sorry

end AbelianMono

section ModuleMono

variable {U X : Scheme.{u}}
variable {Λ : Type w} [Ring Λ]
variable (j : U ⟶ X) [Etale j] [IsSeparated j]

variable
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]

/-- Each component of the module extension-by-zero comparison is a monomorphism. -/
instance moduleExtensionByZeroToDirectImage_app_mono
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ)) :
    Mono ((moduleExtensionByZeroToDirectImage j).app F) := sorry

end ModuleMono

/-- For a finite étale morphism, each component of the abelian extension-by-zero
comparison with small étale direct image is an isomorphism. -/
instance abelianExtensionByZeroToDirectImage_app_isIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsFinite j] [Etale j]
    [∀ G : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{w}) :
    IsIso ((abelianExtensionByZeroToDirectImage j).app F) := sorry

/-- For a finite étale morphism, each component of the `Λ`-module extension-by-zero
comparison with small étale direct image is an isomorphism. -/
instance moduleExtensionByZeroToDirectImage_app_isIso
    {U X : Scheme.{u}} {Λ : Type w} [Ring Λ] (j : U ⟶ X) [IsFinite j] [Etale j]
    [∀ G : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension G]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ)) :
    IsIso ((moduleExtensionByZeroToDirectImage j).app F) := sorry

end AlgebraicGeometry.Scheme
