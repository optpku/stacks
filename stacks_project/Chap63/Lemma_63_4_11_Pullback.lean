module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict
public import stacks_project.Chap63.«63_4_0_2_LowerShriekPresheaf»
public import stacks_project.Chap63.Lemma_63_3_13_LowerShriek

/-!
# Transport of finite-support data along a composition identification

For composable scheme morphisms `f' : X ⟶ Y'` and `g : Y' ⟶ Y`, the site
isomorphism `smallEtalePullbackCompIso f' g` identifies `X_V` with `X_{V'}`.
Admissible locally closed supports finite over `V` transport to admissible
supports finite over `V'`, using separatedness of `g` for finiteness of
`Z → V'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y' Y : Scheme.{u}} (f' : X ⟶ Y') (g : Y' ⟶ Y)
variable [LocallyQuasiFinite f'] [LocallyQuasiFinite (f' ≫ g)]
variable [IsSeparated g]

/-- The scheme morphism `X_V ⟶ X_{V'}` underlying the inverse of
`smallEtalePullbackCompIso f' g` at an étale `Y`-scheme `V`. -/
def compSchemeMap (V : Y.Etale) :
    baseChangeScheme (f' ≫ g) V ⟶
      baseChangeScheme f' ((smallEtalePullback g).obj V) :=
  ((smallEtalePullbackCompIso f' g).inv.app V).left

/-- `compSchemeMap` is the underlying morphism of
`(smallEtalePullbackCompIso f' g).inv` at `V`. -/
theorem compSchemeMap_eq (V : Y.Etale) :
    compSchemeMap f' g V = ((smallEtalePullbackCompIso f' g).inv.app V).left :=
  sorry

/-- The composition identification `X_V ⟶ X_{V'}` is an open immersion. -/
instance isOpenImmersion_compSchemeMap (V : Y.Etale) :
    IsOpenImmersion (compSchemeMap f' g V) :=
  sorry

namespace FiniteSupport

/-- Transport of an admissible support along `X_V ≅ X_{V'}`. -/
def Admissible.comp {V : Y.Etale} (A : Admissible (f' ≫ g) V) :
    Admissible f' ((smallEtalePullback g).obj V) where
  subset := ⟨compSchemeMap f' g V '' (A.subset : Set _), sorry⟩
  ambient := compSchemeMap f' g V ''ᵁ A.ambient
  subset_le_ambient := sorry
  isClosed_in_ambient := sorry
  toBase_isFinite := sorry

/-- Transport of admissible supports records the image locally closed subset
and the image ambient open along `compSchemeMap`. -/
theorem Admissible.comp_spec {V : Y.Etale} (A : Admissible (f' ≫ g) V) :
    ((Admissible.comp f' g A).subset :
        Set (baseChangeScheme f' ((smallEtalePullback g).obj V))) =
      compSchemeMap f' g V '' (A.subset : Set _) ∧
      (Admissible.comp f' g A).ambient = compSchemeMap f' g V ''ᵁ A.ambient :=
  sorry

/-- Transport of admissible supports along `X_V ≅ X_{V'}` is monotone. -/
theorem Admissible.comp_mono {V : Y.Etale} {A B : Admissible (f' ≫ g) V}
    (h : A ≤ B) :
    Admissible.comp f' g A ≤ Admissible.comp f' g B :=
  sorry

/-- The functor on admissible supports induced by transport along
`X_V ≅ X_{V'}`. -/
def Admissible.compFunctor (V : Y.Etale) :
    Admissible (f' ≫ g) V ⥤ Admissible f' ((smallEtalePullback g).obj V) where
  obj := Admissible.comp f' g
  map h := CategoryTheory.homOfLE (Admissible.comp_mono f' g (leOfHom h))
  map_id := sorry
  map_comp := sorry

/-- The composition functor acts by `Admissible.comp`. -/
theorem Admissible.compFunctor_obj (V : Y.Etale) (A : Admissible (f' ≫ g) V) :
    (Admissible.compFunctor f' g V).obj A = Admissible.comp f' g A :=
  sorry

/-- The scheme isomorphism from the ambient open of an admissible support on
`X_V` to its image open on `X_{V'}`. -/
def ambientCompSchemeIso {V : Y.Etale} (A : Admissible (f' ≫ g) V) :
    A.ambient.toScheme ≅ (Admissible.comp f' g A).ambient.toScheme :=
  (compSchemeMap f' g V).isoImage A.ambient

/-- The isomorphism of small-étale `X`-schemes identifying the ambient open of
an admissible support on `X_V` with its image open on `X_{V'}`. -/
def ambientCompIso {V : Y.Etale} (A : Admissible (f' ≫ g) V) :
    mk (A.ambient.ι ≫ baseChangeToSource (f' ≫ g) V) ≅
      mk ((Admissible.comp f' g A).ambient.ι ≫
        baseChangeToSource f' ((smallEtalePullback g).obj V)) :=
  MorphismProperty.Over.isoMk (ambientCompSchemeIso f' g A) sorry

/-- The underlying scheme isomorphism of `ambientCompIso` is the open-image
isomorphism of `compSchemeMap`. -/
theorem ambientCompIso_hom_left {V : Y.Etale} (A : Admissible (f' ≫ g) V) :
    (ambientCompIso f' g A).hom.left = (ambientCompSchemeIso f' g A).hom :=
  sorry

/-- Transport of supported sections `H_Z(F)` along `X_V ≅ X_{V'}`. -/
def sectionsComp (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (A : Admissible (f' ≫ g) V) :
    sections (f' ≫ g) F A ⟶ sections f' F (Admissible.comp f' g A) :=
  AddCommGrpCat.ofHom
    { toFun := fun σ ↦
        ⟨(F.1.mapIso (ambientCompIso f' g A).symm.op).hom.hom σ.1, sorry⟩
      map_zero' := sorry
      map_add' := sorry }

/-- Transport of supported sections acts by the inverse of `ambientCompIso`. -/
theorem sectionsComp_apply (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    {V : Y.Etale} (A : Admissible (f' ≫ g) V)
    (σ : sections (f' ≫ g) F A) :
    ((sectionsComp f' g F A).hom σ).1 =
      (F.1.mapIso (ambientCompIso f' g A).symm.op).hom.hom σ.1 :=
  sorry

/-- The finite-support diagram map sending `H_Z(F)` on `X_V` to `H_Z(F)` on
`X_{V'}`. -/
def diagramComp (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (V : Y.Etale) :
    diagram (f' ≫ g) F V ⟶
      Admissible.compFunctor f' g V ⋙
        diagram f' F ((smallEtalePullback g).obj V) where
  app A := sectionsComp f' g F A
  naturality := sorry

end FiniteSupport

/-- A finite-support pair `(Z, s)` on `X_V` viewed as a pair on `X_{V'}`. -/
def FiniteSupportTerm.comp {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    {V : Y.Etale} (t : FiniteSupportTerm (f' ≫ g) F V) :
    FiniteSupportTerm f' F ((smallEtalePullback g).obj V) where
  subscheme := t.subscheme
  ι := t.ι ≫ compSchemeMap f' g V
  ι_isImmersion := sorry
  toBase_isFinite := sorry
  ambient := compSchemeMap f' g V ''ᵁ t.ambient
  range_subset_ambient := sorry
  isClosed_in_ambient := sorry
  sec :=
    ((FiniteSupport.sectionsComp f' g F
          (FiniteSupport.Admissible.ofTerm (f' ≫ g) t)).hom
        ⟨t.sec, t.mem_sectionsSupportedIn⟩).1
  mem_sectionsSupportedIn := sorry

/-- Composition transport of a finite-support pair records the composed
immersion and the image ambient open. -/
theorem FiniteSupportTerm.comp_spec
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} {V : Y.Etale}
    (t : FiniteSupportTerm (f' ≫ g) F V) :
    (FiniteSupportTerm.comp f' g t).ι = t.ι ≫ compSchemeMap f' g V ∧
      (FiniteSupportTerm.comp f' g t).ambient =
        compSchemeMap f' g V ''ᵁ t.ambient :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
