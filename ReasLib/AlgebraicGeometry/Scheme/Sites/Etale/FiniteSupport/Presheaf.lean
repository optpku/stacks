/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Admissible

/-!
# Compact-support lower shriek as a colimit of `H_Z(F)`

The abelian presheaf `f_p! F` on `Y_étale`, with values the colimit of
supported sections `H_Z(F)` over admissible locally closed subsets of `|X_V|`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace FiniteSupport

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]

/-- The restriction morphism of small-étale `X`-schemes associated to an
inclusion of Zariski opens. -/
def homOfLE {W : Scheme.{u}} (hW : W ⟶ X) [Etale hW] {U V : W.Opens} (h : U ≤ V) :
    mk (U.ι ≫ hW) ⟶ mk (V.ι ≫ hW) :=
  MorphismProperty.Over.homMk (W.homOfLE h) sorry

/-- The underlying scheme morphism of an open restriction is `Scheme.homOfLE`. -/
theorem homOfLE_left {W : Scheme.{u}} (hW : W ⟶ X) [Etale hW] {U V : W.Opens}
    (h : U ≤ V) :
    (homOfLE hW h).left = W.homOfLE h :=
  rfl

/-- The scheme morphism from the inverse image of an open of `X_V` to that open. -/
def preimageSchemeHom {V' V : Y.Etale} (g : V' ⟶ V)
    (U : (baseChangeScheme f V).Opens) :
    (baseChangeSchemeMap f g ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι
    ((baseChangeSchemeMap f g ⁻¹ᵁ U).ι ≫ baseChangeSchemeMap f g) sorry

/-- The morphism of small-étale `X`-schemes from the inverse image of an open of
`X_V` to that open. -/
def preimageHom {V' V : Y.Etale} (g : V' ⟶ V)
    (U : (baseChangeScheme f V).Opens) :
    mk ((baseChangeSchemeMap f g ⁻¹ᵁ U).ι ≫ baseChangeToSource f V') ⟶
      mk (U.ι ≫ baseChangeToSource f V) :=
  MorphismProperty.Over.homMk (preimageSchemeHom f g U) sorry

/-- The underlying scheme morphism of `preimageHom` is the open-immersion lift
along `X_{V'} ⟶ X_V`. -/
theorem preimageHom_left {V' V : Y.Etale} (g : V' ⟶ V)
    (U : (baseChangeScheme f V).Opens) :
    (preimageHom f g U).left = preimageSchemeHom f g U :=
  rfl

/-- The group `H_Z(F)` of supported sections, as an object of `AddCommGrpCat`. -/
def sections (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (A : Admissible f V) : AddCommGrpCat.{u} :=
  FiniteSupportColimit.sections f F (AdmissiblePresentation.toIndex f A)

/-- The compact-support group associated to an admissible support is `H_Z(F)`. -/
theorem sections_eq (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (A : Admissible f V) :
    sections f F A =
      AddCommGrpCat.of
        (sectionsSupportedIn F (baseChangeToSource f V) A.subset A.ambient
          A.subset_le_ambient A.isClosed_in_ambient) :=
  rfl

/-- Membership in `H_Z(F)` is the supported-section condition on the ambient
open. -/
theorem mem_sections (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (A : Admissible f V)
    (σ : F.1.obj (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))) :
    σ ∈ sectionsSupportedIn F (baseChangeToSource f V) A.subset A.ambient
      A.subset_le_ambient A.isClosed_in_ambient ↔
      A.ambient.ι ''
          (abelianSheafSectionSupport F (mk (A.ambient.ι ≫ baseChangeToSource f V)) σ :
            Set (mk (A.ambient.ι ≫ baseChangeToSource f V)).left) ⊆
        (A.subset : Set (baseChangeScheme f V)) :=
  FiniteSupportColimit.mem_sections_iff f F (AdmissiblePresentation.toIndex f A) σ

/-- Restriction of supported sections along an inequality of admissible
supports. -/
def sectionsMap (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    {A B : Admissible f V} (h : A ≤ B) :
    sections f F A ⟶ sections f F B :=
  FiniteSupportColimit.sectionsMap f F h

/-- The diagram of abelian groups `Z ↦ H_Z(F)` indexed by admissible supports on
`X_V`. -/
def diagram (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    Admissible f V ⥤ AddCommGrpCat.{u} :=
  Admissible.toIndexFunctor f V ⋙ FiniteSupportColimit.diagram f F V

/-- The finite-support diagram evaluates as `H_Z(F)` at an admissible support. -/
theorem diagram_obj (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (A : Admissible f V) :
    (diagram f F V).obj A = sections f F A :=
  rfl

/-- Restriction of supported sections from `X_V` to `X_{V'}`. -/
def restriction (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V' V : Y.Etale} (g : V' ⟶ V) :
    diagram f F V ⟶ Admissible.pullbackFunctor f g ⋙ diagram f F V' where
  app A :=
    AddCommGrpCat.ofHom
      { toFun := fun σ ↦
          ⟨(F.1.map (preimageHom f g A.ambient).op).hom σ.1, sorry⟩
        map_zero' := sorry
        map_add' := sorry }
  naturality := sorry

/-- Restriction of supported sections is natural in admissible supports. -/
theorem restriction_naturality (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V' V : Y.Etale} (g : V' ⟶ V) {A B : Admissible f V} (h : A ⟶ B) :
    (diagram f F V).map h ≫ (restriction f F g).app B =
      (restriction f F g).app A ≫
        ((Admissible.pullbackFunctor f g ⋙ diagram f F V').map h) :=
  (restriction f F g).naturality h

/-- A morphism of abelian sheaves induces a morphism of finite-support diagrams. -/
def mapDiagram {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G)
    (V : Y.Etale) : diagram f F V ⟶ diagram f G V where
  app A :=
    AddCommGrpCat.ofHom
      { toFun := fun σ ↦
          ⟨(φ.hom.app (op (mk (A.ambient.ι ≫ baseChangeToSource f V)))).hom σ.1,
            sorry⟩
        map_zero' := sorry
        map_add' := sorry }
  naturality := sorry

/-- The identity sheaf morphism induces the identity on finite-support
diagrams. -/
theorem mapDiagram_id (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) :
    mapDiagram f (𝟙 F) V = 𝟙 (diagram f F V) :=
  sorry

/-- A finite-support pair `(Z, s)` maps to the class of `s` in the colimit of
`H_Z(F)`. -/
def ofTerm (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (t : FiniteSupportTerm f F V) :=
  (colimit.ι (diagram f F V) (Admissible.ofTerm f t)).hom
    ⟨t.sec, t.mem_sectionsSupportedIn⟩

/-- The coprojection of a finite-support pair is the colimit coprojection of its
section. -/
theorem ofTerm_eq (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (t : FiniteSupportTerm f F V) :
    ofTerm f F V t =
      (colimit.ι (diagram f F V) (Admissible.ofTerm f t))
        ⟨t.sec, t.mem_sectionsSupportedIn⟩ :=
  rfl

/-- Enlarging the support of a section does not change its class in
`f_p! F(V)`. -/
theorem ofTerm_enlargement (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) {A B : Admissible f V} (h : A ≤ B) (σ : sections f F A) :
    (colimit.ι (diagram f F V) B) (sectionsMap f F h σ) =
      (colimit.ι (diagram f F V) A) σ :=
  sorry

/-- Adding sections with the same admissible support is preserved in
`f_p! F(V)`. -/
theorem ofTerm_add (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (A : Admissible f V) (σ τ : sections f F A) :
    (colimit.ι (diagram f F V) A) (σ + τ) =
      (colimit.ι (diagram f F V) A) σ + (colimit.ι (diagram f F V) A) τ :=
  sorry

/-- A finite formal sum maps to the corresponding linear combination in the
colimit of `H_Z(F)`. -/
def ofFormalSum (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (s : FiniteSupportFormalSum f F V) :=
  FreeAbelianGroup.lift (ofTerm f F V) s

/-- The formal-sum comparison is the induced map from the free abelian group on
admissible pairs. -/
theorem ofFormalSum_eq (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) (s : FiniteSupportFormalSum f F V) :
    ofFormalSum f F V s = FreeAbelianGroup.lift (ofTerm f F V) s :=
  rfl

end FiniteSupport

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]

/-- The presheaf `f_p!` of abelian groups, sending `V` to the colimit of
`H_Z(F)` over admissible locally closed subsets of `|X_V|`. -/
def lowerShriekPresheaf :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj F :=
    { obj := fun V ↦ colimit (FiniteSupport.diagram f F V.unop)
      map := fun {V W} g ↦
        colimMap (FiniteSupport.restriction f F g.unop) ≫
          colimit.pre (FiniteSupport.diagram f F W.unop)
            (FiniteSupport.Admissible.pullbackFunctor f g.unop)
      map_id := sorry
      map_comp := sorry }
  map {F G} φ :=
    { app := fun V ↦ colimMap (FiniteSupport.mapDiagram f φ V.unop)
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Evaluating the compact-support presheaf at `V` is the colimit of `H_Z(F)`
over admissible supports on `X_V`. -/
theorem lowerShriekPresheaf_obj_colimit
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale) :
    ((lowerShriekPresheaf f).obj F).obj (op V) =
      colimit (FiniteSupport.diagram f F V) :=
  rfl

end AlgebraicGeometry.Scheme.Etale

end
