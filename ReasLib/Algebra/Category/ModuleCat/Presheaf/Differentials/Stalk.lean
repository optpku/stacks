/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Derivation.Stalk
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of presheaves of relative differentials

For a morphism of commutative-ring presheaves on a topological space, the stalk of the
sectionwise Kahler-differential presheaf is canonically the module of Kahler differentials of the
induced morphism on stalk rings.  The forward map is obtained from the cocone of neighborhood
comparisons, while the inverse is induced by the universal derivation on the stalk.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u

namespace PresheafOfModules.RelativeDifferentials.Stalk

variable {X : TopCat.{u}} {R S : X.Presheaf CommRingCat.{u}}

/-- The morphism on stalk rings induced by a morphism of commutative-ring presheaves. -/
abbrev ringMap (f : R ⟶ S) (x : X) : R.stalk x ⟶ S.stalk x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f

/-- The stalk of the sectionwise relative-differentials presheaf. -/
noncomputable abbrev source (f : R ⟶ S) (x : X) : ModuleCat (S.stalk x) :=
  PresheafOfModules.stalkModuleCatOfCommRing (relativeDifferentials' f) x

/-- The relative differentials of the morphism induced on stalk rings. -/
noncomputable abbrev target (f : R ⟶ S) (x : X) : ModuleCat (S.stalk x) :=
  CommRingCat.KaehlerDifferential (ringMap f x)

/-- The relative derivation on stalk rings obtained from the sectionwise universal derivation. -/
noncomputable abbrev derivation (f : R ⟶ S) (x : X) :
    (source f x).Derivation (ringMap f x) :=
  (derivation' f).stalk x

/-- The map from the relative differentials on one neighborhood to the relative differentials
of the induced morphism on stalk rings. -/
noncomputable def leg (f : R ⟶ S) (x : X) (U : (OpenNhds x)ᵒᵖ) :
    (((OpenNhds.inclusion x).op ⋙
      (relativeDifferentials' f).presheaf).obj U) ⟶
      (forget₂ (ModuleCat (S.stalk x)) AddCommGrpCat.{u}).obj (target f x) :=
  AddCommGrpCat.ofHom
    (CommRingCat.KaehlerDifferential.map
      (g' := S.germ U.unop.1 x U.unop.2)
      (TopCat.Presheaf.stalkFunctor_map_germ
        U.unop.1 x U.unop.2 f)).hom.toAddMonoidHom

/-- A neighborhood comparison sends the differential of a section to the differential of its
germ. -/
theorem leg_d (f : R ⟶ S) (x : X) (U : (OpenNhds x)ᵒᵖ)
    (r : S.obj (op U.unop.1)) :
    leg f x U (CommRingCat.KaehlerDifferential.d r) =
      CommRingCat.KaehlerDifferential.d
        (S.germ U.unop.1 x U.unop.2 r) := sorry

/-- The neighborhood differential comparisons are compatible with restriction. -/
theorem leg_naturality (f : R ⟶ S) (x : X)
    {U V : (OpenNhds x)ᵒᵖ} (i : U ⟶ V) :
    (((OpenNhds.inclusion x).op ⋙
      (relativeDifferentials' f).presheaf).map i) ≫ leg f x V =
        leg f x U := sorry

/-- The cocone of neighborhood relative-differential modules with vertex the relative
differentials of the morphism on stalk rings. -/
noncomputable def cocone (f : R ⟶ S) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙
      (relativeDifferentials' f).presheaf) where
  pt := (forget₂ (ModuleCat (S.stalk x)) AddCommGrpCat.{u}).obj (target f x)
  ι :=
    { app := leg f x
      naturality := fun _ _ i ↦ leg_naturality f x i }

/-- The additive comparison from the stalk of the sectionwise relative-differentials presheaf to
the relative differentials of the morphism on stalk rings. -/
noncomputable def addMap (f : R ⟶ S) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (relativeDifferentials' f).presheaf x ⟶
      (forget₂ (ModuleCat (S.stalk x)) AddCommGrpCat.{u}).obj (target f x) :=
  colimit.desc _ (cocone f x)

/-- The additive stalk comparison preserves addition. -/
theorem addMap_add (f : R ⟶ S) (x : X) (m n : source f x) :
    addMap f x (m + n) = addMap f x m + addMap f x n := sorry

/-- The additive stalk comparison is linear over the target-ring stalk. -/
theorem addMap_smul (f : R ⟶ S) (x : X) (r : S.stalk x) (m : source f x) :
    addMap f x (r • m) =
      HSMul.hSMul (α := S.stalk x) (β := target f x) r (addMap f x m) := sorry

/-- The canonical comparison from the stalk of the sectionwise relative-differentials presheaf
to the relative differentials of the morphism on stalk rings. -/
@[stacks 08TE "presheaf differential stalk comparison"]
noncomputable def comparison (f : R ⟶ S) (x : X) : source f x ⟶ target f x :=
  ModuleCat.ofHom
    { toFun := addMap f x
      map_add' := addMap_add f x
      map_smul' := addMap_smul f x }

/-- The presheaf stalk comparison sends the germ of an objectwise universal differential to the
universal differential of the corresponding germ. -/
@[stacks 08TE "presheaf differential stalk comparison on generators"]
theorem comparison_germ_d (f : R ⟶ S) (x : X)
    (U : Opens X) (hx : x ∈ U) (r : S.obj (op U)) :
    comparison f x
        (TopCat.Presheaf.germ (relativeDifferentials' f).presheaf U x hx
          (CommRingCat.KaehlerDifferential.d r)) =
      CommRingCat.KaehlerDifferential.d (S.germ U x hx r) := sorry

/-- The canonical comparison from the relative differentials of the stalk-ring morphism to the
stalk of the sectionwise relative-differentials presheaf. -/
@[stacks 08TE "inverse presheaf differential stalk comparison"]
noncomputable abbrev comparisonInv (f : R ⟶ S) (x : X) :
    target f x ⟶ source f x :=
  (derivation f x).desc

/-- The inverse presheaf comparison sends a universal differential to the induced stalk
derivation. -/
@[simp]
theorem comparisonInv_d (f : R ⟶ S) (x : X) (r : S.stalk x) :
    comparisonInv f x (CommRingCat.KaehlerDifferential.d r) =
      (derivation f x).d r := sorry

/-- The stalk derivation sends the germ of a section to the germ of its objectwise universal
differential. -/
theorem derivation_d_germ (f : R ⟶ S) (x : X)
    (U : Opens X) (hx : x ∈ U) (r : S.obj (op U)) :
    (derivation f x).d (S.germ U x hx r) =
      TopCat.Presheaf.germ (relativeDifferentials' f).presheaf U x hx
        (CommRingCat.KaehlerDifferential.d r) := sorry

/-- The comparison from stalk-ring differentials sends a differential of a germ to the germ of
the corresponding objectwise differential. -/
@[stacks 08TE "inverse presheaf comparison on germ differentials", simp]
theorem comparisonInv_d_germ (f : R ⟶ S) (x : X)
    (U : Opens X) (hx : x ∈ U) (r : S.obj (op U)) :
    comparisonInv f x
        (CommRingCat.KaehlerDifferential.d (S.germ U x hx r)) =
      TopCat.Presheaf.germ (relativeDifferentials' f).presheaf U x hx
        (CommRingCat.KaehlerDifferential.d r) := sorry

/-- The forward presheaf comparison followed by its inverse is the identity. -/
@[simp]
theorem comparison_comp_comparisonInv (f : R ⟶ S) (x : X) :
    comparison f x ≫ comparisonInv f x = 𝟙 (source f x) := sorry

/-- The inverse presheaf comparison followed by the forward comparison is the identity. -/
@[simp]
theorem comparisonInv_comp_comparison (f : R ⟶ S) (x : X) :
    comparisonInv f x ≫ comparison f x = 𝟙 (target f x) := sorry

/-- The stalk of the sectionwise relative-differentials presheaf is canonically isomorphic to
the relative differentials of the morphism on stalk rings. -/
@[stacks 08TE "presheaf differential stalk isomorphism"]
noncomputable def comparisonIso (f : R ⟶ S) (x : X) : source f x ≅ target f x where
  hom := comparison f x
  inv := comparisonInv f x
  hom_inv_id := comparison_comp_comparisonInv f x
  inv_hom_id := comparisonInv_comp_comparison f x

/-- The forward map of the presheaf differential stalk isomorphism is the cocone comparison. -/
@[simp]
theorem comparisonIso_hom (f : R ⟶ S) (x : X) :
    (comparisonIso f x).hom = comparison f x := sorry

/-- The inverse of the presheaf differential stalk isomorphism is induced by the universal stalk
derivation. -/
@[simp]
theorem comparisonIso_inv (f : R ⟶ S) (x : X) :
    (comparisonIso f x).inv = comparisonInv f x := sorry

/-- The forward presheaf differential stalk comparison is an isomorphism. -/
instance comparison_isIso (f : R ⟶ S) (x : X) : IsIso (comparison f x) := sorry

/-- The inverse presheaf differential stalk comparison is an isomorphism. -/
instance comparisonInv_isIso (f : R ⟶ S) (x : X) : IsIso (comparisonInv f x) := sorry

end PresheafOfModules.RelativeDifferentials.Stalk

-- The non-Prop maps below are constructed from neighborhood germs, colimits, and universal
-- derivations. Any `sorryAx` is confined to compatibility, linearity, and inverse-law proofs.
