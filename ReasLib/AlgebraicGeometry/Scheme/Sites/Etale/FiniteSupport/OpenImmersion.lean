module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Presheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.OpenImmersion
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

/-!
# Covariance of finite-support presheaves along open immersions

Image transport of admissible supports and their sections constructs covariance
of finite-support presheaves, preserving formal sums and composition.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X' X Y : Scheme.{u}} (j : X' ⟶ X) (f : X ⟶ Y)
variable [IsOpenImmersion j] [LocallyQuasiFinite f]

/-- The scheme morphism `X'_V ⟶ X_V` underlying `openImmersionPullback` at `V`. -/
def openImmersionBaseChange (V : Y.Etale) :
    baseChangeScheme (j ≫ f) V ⟶ baseChangeScheme f V :=
  ((openImmersionPullback j f).app V).left

/-- The base-change morphism `X'_V ⟶ X_V` of an open immersion of the source is
an open immersion. -/
instance isOpenImmersion_openImmersionBaseChange (V : Y.Etale) :
    IsOpenImmersion (openImmersionBaseChange j f V) :=
  isOpenImmersion_openImmersionPullback_app j f V

/-- Compact-support presheaf is unchanged when the scheme morphism is replaced
by an equal morphism. -/
def lowerShriekPresheafCongr {X Y : Scheme.{u}} {g h : X ⟶ Y}
    [LocallyQuasiFinite g] [LocallyQuasiFinite h] (e : g = h) :
    lowerShriekPresheaf g ≅ lowerShriekPresheaf h :=
  eqToIso (e ▸ rfl)

namespace FiniteSupport

/-- Pushforward of an admissible support along `X'_V ⟶ X_V`. -/
def Admissible.openImmersion {V : Y.Etale} (A : Admissible (j ≫ f) V) :
    Admissible f V where
  subset := ⟨openImmersionBaseChange j f V '' (A.subset : Set _), sorry⟩
  ambient := openImmersionBaseChange j f V ''ᵁ A.ambient
  subset_le_ambient := sorry
  isClosed_in_ambient := sorry
  toBase_isFinite := sorry

/-- Pushforward of admissible supports records the image locally closed subset
and the image ambient open. -/
theorem Admissible.openImmersion_spec {V : Y.Etale} (A : Admissible (j ≫ f) V) :
    ((Admissible.openImmersion j f A).subset : Set (baseChangeScheme f V)) =
        openImmersionBaseChange j f V '' (A.subset : Set _) ∧
      (Admissible.openImmersion j f A).ambient =
        openImmersionBaseChange j f V ''ᵁ A.ambient :=
  ⟨rfl, rfl⟩

/-- Pushforward of admissible supports is monotone. -/
theorem Admissible.openImmersion_mono {V : Y.Etale} {A B : Admissible (j ≫ f) V}
    (h : A ≤ B) :
    Admissible.openImmersion j f A ≤ Admissible.openImmersion j f B :=
  sorry

/-- The functor on admissible supports induced by pushforward along
`X'_V ⟶ X_V`. -/
def admissibleOpenImmersion (V : Y.Etale) :
    Admissible (j ≫ f) V ⥤ Admissible f V where
  obj := Admissible.openImmersion j f
  map h := CategoryTheory.homOfLE (Admissible.openImmersion_mono j f (leOfHom h))
  map_id := fun _ ↦ Subsingleton.elim _ _
  map_comp := fun _ _ ↦ Subsingleton.elim _ _

/-- The admissible-support functor acts by image of locally closed subsets. -/
theorem admissibleOpenImmersion_obj (V : Y.Etale) (A : Admissible (j ≫ f) V) :
    (admissibleOpenImmersion j f V).obj A = Admissible.openImmersion j f A :=
  rfl

/-- The morphism of small-étale `X`-schemes identifying the ambient open of an
admissible support on `X'_V` with its image open on `X_V`. -/
def ambientOpenImmersionIso {V : Y.Etale} (A : Admissible (j ≫ f) V) :
    mk ((openImmersionBaseChange j f V ''ᵁ A.ambient).ι ≫ baseChangeToSource f V) ≅
      (etaleRestriction j).obj
        (mk (A.ambient.ι ≫ baseChangeToSource (j ≫ f) V)) :=
  MorphismProperty.Over.isoMk
    ((openImmersionBaseChange j f V).isoImage A.ambient).symm sorry

/-- Identification `H_Z(F|_{X'}) ≅ H_Z(F)` of supported-section groups along
the open immersion `X'_V ⟶ X_V`. -/
def sectionsOpenImmersion (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (A : Admissible (j ≫ f) V) :
    sections (j ≫ f) ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) A ≅
      sections f F ((admissibleOpenImmersion j f V).obj A) where
  hom :=
    AddCommGrpCat.ofHom
      { toFun := fun σ ↦
          ⟨((etaleRestriction j).sheafPushforwardContinuousObjObjIso
                  AddCommGrpCat.{u} F
                  (mk (A.ambient.ι ≫ baseChangeToSource (j ≫ f) V)) ≪≫
                (F.1.mapIso (ambientOpenImmersionIso j f A).op)).hom.hom σ.1,
            sorry⟩
        map_zero' := sorry
        map_add' := sorry }
  inv :=
    AddCommGrpCat.ofHom
      { toFun := fun σ ↦
          ⟨((etaleRestriction j).sheafPushforwardContinuousObjObjIso
                  AddCommGrpCat.{u} F
                  (mk (A.ambient.ι ≫ baseChangeToSource (j ≫ f) V)) ≪≫
                (F.1.mapIso (ambientOpenImmersionIso j f A).op)).inv.hom σ.1,
            sorry⟩
        map_zero' := sorry
        map_add' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `sectionsOpenImmersion` is transport of supported
sections along `ambientOpenImmersionIso`. -/
theorem sectionsOpenImmersion_hom_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) {V : Y.Etale}
    (A : Admissible (j ≫ f) V)
    (σ : sections (j ≫ f) ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) A) :
    ((sectionsOpenImmersion j f F A).hom.hom σ).1 =
      ((etaleRestriction j).sheafPushforwardContinuousObjObjIso AddCommGrpCat.{u} F
            (mk (A.ambient.ι ≫ baseChangeToSource (j ≫ f) V)) ≪≫
          (F.1.mapIso (ambientOpenImmersionIso j f A).op)).hom.hom σ.1 :=
  rfl

/-- The finite-support diagram map sending `H_Z(F|_{X'})` to `H_Z(F)`. -/
def diagramOpenImmersion (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) :
    diagram (j ≫ f) ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V ⟶
      admissibleOpenImmersion j f V ⋙ diagram f F V where
  app A := (sectionsOpenImmersion j f F A).hom
  naturality := sorry

end FiniteSupport

/-- A finite-support pair `(Z', s')` on `X'_V` viewed as a pair on `X_V`. -/
def FiniteSupportTerm.openImmersion {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    {V : Y.Etale}
    (t : FiniteSupportTerm (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    FiniteSupportTerm f F V where
  subscheme := t.subscheme
  ι := t.ι ≫ openImmersionBaseChange j f V
  ι_isImmersion := sorry
  toBase_isFinite := sorry
  ambient := openImmersionBaseChange j f V ''ᵁ t.ambient
  range_subset_ambient := sorry
  isClosed_in_ambient := sorry
  sec :=
    ((FiniteSupport.sectionsOpenImmersion j f F
          (FiniteSupport.Admissible.ofTerm (j ≫ f) t)).hom.hom
        ⟨t.sec, t.mem_sectionsSupportedIn⟩).1
  mem_sectionsSupportedIn := sorry

/-- Open-immersion pushforward of a finite-support pair records the composed
immersion and the image ambient open. -/
theorem FiniteSupportTerm.openImmersion_spec
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} {V : Y.Etale}
    (t : FiniteSupportTerm (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    (FiniteSupportTerm.openImmersion j f t).ι =
        t.ι ≫ openImmersionBaseChange j f V ∧
      (FiniteSupportTerm.openImmersion j f t).ambient =
        openImmersionBaseChange j f V ''ᵁ t.ambient :=
  ⟨rfl, rfl⟩

/-- Canonical covariance `f'_{p!}(F|_{X'}) ⟶ f_{p!} F` of compact-support
presheaves along an open immersion of the source, as a natural transformation
in the abelian sheaf `F`. -/
def lowerShriekPresheafOpenImmersion :
    etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙ lowerShriekPresheaf (j ≫ f) ⟶
      lowerShriekPresheaf f where
  app F :=
    { app := fun V ↦
        colimMap (FiniteSupport.diagramOpenImmersion j f F V.unop) ≫
          colimit.pre (FiniteSupport.diagram f F V.unop)
            (FiniteSupport.admissibleOpenImmersion j f V.unop)
      naturality := sorry }
  naturality := sorry

/-- The presheaf covariance sends a finite formal sum of pairs on `X'_V` to the
same formal sum of pairs viewed on `X_V`. -/
theorem lowerShriekPresheafOpenImmersion_ofFormalSum
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (V : Y.Etale)
    (s : FiniteSupportFormalSum (j ≫ f)
      ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V) :
    ((lowerShriekPresheafOpenImmersion j f).app F).app (op V)
        (FiniteSupport.ofFormalSum (j ≫ f)
          ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F) V s) =
      FiniteSupport.ofFormalSum f F V
        (FreeAbelianGroup.map (FiniteSupportTerm.openImmersion j f) s) :=
  sorry

/-- Nested covariance of compact-support presheaves along `X'' ⟶ X' ⟶ X`. -/
theorem lowerShriekPresheafOpenImmersion_comp {X'' : Scheme.{u}} (j' : X'' ⟶ X')
    [IsOpenImmersion j'] :
    whiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
          (lowerShriekPresheafOpenImmersion j' (j ≫ f)) ≫
        lowerShriekPresheafOpenImmersion j f =
      whiskerRight (etaleAbelianRestrictionSheafCompIso j j').hom
          (lowerShriekPresheaf (j' ≫ j ≫ f)) ≫
        whiskerLeft (etaleRestrictionSheaf (j' ≫ j) AddCommGrpCat.{u})
          (lowerShriekPresheafCongr (Category.assoc j' j f).symm).hom ≫
          lowerShriekPresheafOpenImmersion (j' ≫ j) f :=
  sorry

variable [IsSeparated f] [LocallyOfFiniteType f]

/-- For a separated morphism, finite-support covariance agrees with compact-support
covariance through the canonical comparison from finite-support presheaves. -/
theorem lowerShriekPresheafOpenImmersion_separated :
    CommSq (lowerShriekPresheafOpenImmersion j f)
      (whiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
        (lowerShriekPresheafComparison (j ≫ f)))
      (lowerShriekPresheafComparison f)
      (whiskerRight (etaleLowerShriekOpenImmersion j f)
        (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u})) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end

end
