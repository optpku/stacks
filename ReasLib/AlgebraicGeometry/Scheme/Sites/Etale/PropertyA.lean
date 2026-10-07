module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u w

namespace AlgebraicGeometry

/-- A morphism has Property (A) when every small étale object admits the prescribed
binary coproduct decomposition after étale base change, together with a point above
each chosen point. -/
def hasPropertyA {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (U : X.Etale) (u : U.left),
    ∃ (V : Y.Etale) (W W' : Scheme.{u})
      (e : W ⨿ W' ≅ pullback f V.hom) (h : W ⟶ U.left),
        h ≫ U.hom = coprod.inl ≫ e.hom ≫ pullback.fst f V.hom ∧
        ∃ w : W, h.base w = u

/-- A separated locally quasi-finite morphism has Property (A). -/
theorem hasPropertyA_of_separated_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyQuasiFinite f] :
    hasPropertyA f := sorry

/-- An integral morphism of schemes has Property (A). -/
theorem hasPropertyA_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    hasPropertyA f := sorry

/-- The additive sheaf direct image induced by pullback on the small étale sites. -/
abbrev smallAbelianPushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P] :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{w} ⥤
      Sheaf Y.smallEtaleTopology AddCommGrpCat.{w} :=
  (Scheme.smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{w}
    Y.smallEtaleTopology X.smallEtaleTopology

/-- Under Property (A), the additive small étale direct image reflects monomorphisms. -/
theorem smallAbelianPushforward_reflectsMonomorphisms
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (hA : hasPropertyA f) :
    (smallAbelianPushforward f).ReflectsMonomorphisms := sorry

/-- Under Property (A), the additive small étale direct image reflects epimorphisms. -/
theorem smallAbelianPushforward_reflectsEpimorphisms
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (hA : hasPropertyA f) :
    (smallAbelianPushforward f).ReflectsEpimorphisms := sorry

/-- Under Property (A), every component of the additive small étale counit is epic. -/
theorem smallAbelianPushforward_counit_epi
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (hA : hasPropertyA f) :
    ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w},
      Epi (((Scheme.smallEtalePullback f).sheafAdjunctionContinuous
        AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology).counit.app F) := sorry

/-- Under Property (A), the additive small étale direct image is faithful. -/
theorem smallAbelianPushforward_faithful
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (hA : hasPropertyA f) :
    (smallAbelianPushforward f).Faithful := sorry

namespace SmallAbelianPushforward

/-- For an integral or separated locally quasi-finite morphism, every component
of the additive small étale counit is epic. -/
theorem counit_epi
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (h_geometric : IsIntegralHom f ∨ (IsSeparated f ∧ LocallyQuasiFinite f)) :
    ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w},
      Epi (((Scheme.smallEtalePullback f).sheafAdjunctionContinuous
        AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology).counit.app F) := sorry

/-- For an integral or separated locally quasi-finite morphism, the additive
small étale direct image is faithful. -/
theorem faithful
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (h_geometric : IsIntegralHom f ∨ (IsSeparated f ∧ LocallyQuasiFinite f)) :
    (smallAbelianPushforward f).Faithful := sorry

/-- For an integral or separated locally quasi-finite morphism, the additive
small étale direct image reflects monomorphisms. -/
theorem reflectsMonomorphisms
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (h_geometric : IsIntegralHom f ∨ (IsSeparated f ∧ LocallyQuasiFinite f)) :
    (smallAbelianPushforward f).ReflectsMonomorphisms := sorry

/-- For an integral or separated locally quasi-finite morphism, the additive
small étale direct image reflects epimorphisms. -/
theorem reflectsEpimorphisms
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (h_geometric : IsIntegralHom f ∨ (IsSeparated f ∧ LocallyQuasiFinite f)) :
    (smallAbelianPushforward f).ReflectsEpimorphisms := sorry

/-- Faithfulness of the additive small étale direct image for an integral
morphism. -/
instance faithful_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    [IsIntegralHom f] :
    (smallAbelianPushforward f).Faithful :=
  faithful f (Or.inl inferInstance)

/-- Faithfulness of the additive small étale direct image for a separated
locally quasi-finite morphism. -/
instance faithful_of_separated_locallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    [IsSeparated f] [LocallyQuasiFinite f] :
    (smallAbelianPushforward f).Faithful :=
  faithful f (Or.inr ⟨inferInstance, inferInstance⟩)

/-- For an integral morphism, every component of the additive small étale counit is epic. -/
instance counit_epi_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    [IsIntegralHom f] (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) :
    Epi (((Scheme.smallEtalePullback f).sheafAdjunctionContinuous
      AddCommGrpCat.{w} Y.smallEtaleTopology X.smallEtaleTopology).counit.app F) := sorry

/-- For an integral morphism, the additive small étale direct image reflects monomorphisms. -/
theorem reflectsMonomorphisms_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    [IsIntegralHom f] :
    (smallAbelianPushforward f).ReflectsMonomorphisms := sorry

/-- For an integral morphism, the additive small étale direct image reflects epimorphisms. -/
theorem reflectsEpimorphisms_of_isIntegralHom
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    [IsIntegralHom f] :
    (smallAbelianPushforward f).ReflectsEpimorphisms := sorry

end SmallAbelianPushforward

end AlgebraicGeometry
