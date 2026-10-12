/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Differentials.Stalk
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials

/-!
# Stalks of relative differentials

The presheaf-level theorem that relative differentials commute with stalks combines with the
module-sheafification stalk isomorphism to identify the stalk of a relative-differentials sheaf.
Both directions are explicit composites, and the universal derivation characterizes the inverse
comparison on differentials.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u

namespace TopCat.Sheaf.RelativeDifferentials.Stalk

variable {X : TopCat.{u}} {O₁ O₂ : X.Sheaf CommRingCat.{u}}

/-- The morphism on stalk rings induced by a morphism of sheaves of commutative rings. -/
abbrev ringMap (φ : O₁ ⟶ O₂) (x : X) :
    O₁.presheaf.stalk x ⟶ O₂.presheaf.stalk x :=
  PresheafOfModules.RelativeDifferentials.Stalk.ringMap φ.hom x

/-- The stalk module of the sheaf of relative differentials. -/
noncomputable abbrev source (φ : O₁ ⟶ O₂) (x : X) :
    ModuleCat (O₂.presheaf.stalk x) :=
  (SheafOfModules.stalkFunctorOfCommRing O₂ x).obj
    (TopCat.Sheaf.relativeDifferentials φ)

/-- The module of Kahler differentials of the induced morphism on stalk rings. -/
noncomputable abbrev target (φ : O₁ ⟶ O₂) (x : X) :
    ModuleCat (O₂.presheaf.stalk x) :=
  PresheafOfModules.RelativeDifferentials.Stalk.target φ.hom x

/-- The canonical isomorphism from the stalk of the objectwise relative-differentials presheaf
to the stalk of its sheafification. -/
@[stacks 0D09 "relative-differentials sheafification stalk isomorphism"]
noncomputable abbrev sheafificationIso (φ : O₁ ⟶ O₂) (x : X) :=
  TopCat.Sheaf.moduleSheafificationStalkIso O₂
    (relativeDifferentials' φ.hom) x

/-- The derivation on stalks induced by the universal relative derivation. -/
noncomputable abbrev derivation (φ : O₁ ⟶ O₂) (x : X) :
    (source φ x).Derivation (ringMap φ x) :=
  (TopCat.Sheaf.relativeDifferential φ).stalk x

/-- The canonical forward comparison from the stalk of the relative-differentials sheaf to the
relative differentials of the morphism on stalk rings. -/
@[stacks 08TE "forward stalk comparison map"]
noncomputable def comparison (φ : O₁ ⟶ O₂) (x : X) :
    source φ x ⟶ target φ x :=
  (sheafificationIso φ x).inv ≫
    PresheafOfModules.RelativeDifferentials.Stalk.comparison φ.hom x

/-- The inverse comparison from differentials of the stalk rings to the stalk of the
relative-differentials sheaf. -/
@[stacks 08TE "inverse stalk comparison map"]
noncomputable def comparisonInv (φ : O₁ ⟶ O₂) (x : X) :
    target φ x ⟶ source φ x :=
  PresheafOfModules.RelativeDifferentials.Stalk.comparisonInv φ.hom x ≫
    (sheafificationIso φ x).hom

/-- The forward comparison followed by the inverse comparison is the
identity on the stalk of the relative-differentials sheaf. -/
@[simp]
theorem comparison_comp_comparisonInv (φ : O₁ ⟶ O₂) (x : X) :
    comparison φ x ≫ comparisonInv φ x = 𝟙 (source φ x) := sorry

/-- The inverse comparison followed by the forward comparison is the
identity on the differentials of the stalk rings. -/
@[simp]
theorem comparisonInv_comp_comparison (φ : O₁ ⟶ O₂) (x : X) :
    comparisonInv φ x ≫ comparison φ x = 𝟙 (target φ x) := sorry

/-- The canonical forward stalk comparison is an isomorphism. -/
instance comparison_isIso (φ : O₁ ⟶ O₂) (x : X) :
    IsIso (comparison φ x) := sorry

/-- The inverse stalk comparison is an isomorphism. -/
instance comparisonInv_isIso (φ : O₁ ⟶ O₂) (x : X) :
    IsIso (comparisonInv φ x) := sorry

/-- The stalk of the sheaf of relative differentials is canonically isomorphic to the module of
Kähler differentials for the induced morphism between stalk rings. -/
@[stacks 08TE]
noncomputable def iso (φ : O₁ ⟶ O₂) (x : X) :
    source φ x ≅ target φ x :=
  (sheafificationIso φ x).symm ≪≫
    PresheafOfModules.RelativeDifferentials.Stalk.comparisonIso φ.hom x

/-- The forward map of the stalk relative-differentials isomorphism is the canonical forward
comparison. -/
@[stacks 08TE "stalk comparison isomorphism hom", simp]
theorem iso_hom (φ : O₁ ⟶ O₂) (x : X) :
    (iso φ x).hom = comparison φ x := sorry

/-- The inverse of the stalk relative-differentials isomorphism is the inverse comparison. -/
@[stacks 08TE "stalk comparison isomorphism inverse", simp]
theorem iso_inv (φ : O₁ ⟶ O₂) (x : X) :
    (iso φ x).inv = comparisonInv φ x := sorry

/-- The forward comparison sends the induced stalk derivation of an element to its universal
differential. -/
@[stacks 08TE "forward stalk comparison on differentials", simp]
theorem comparison_d (φ : O₁ ⟶ O₂) (x : X) (r : O₂.presheaf.stalk x) :
    comparison φ x ((derivation φ x).d r) =
      CommRingCat.KaehlerDifferential.d r := sorry

/-- The inverse comparison sends a universal differential of a stalk element to the induced
stalk derivation. -/
@[stacks 08TE "inverse stalk comparison on differentials", simp]
theorem comparisonInv_d (φ : O₁ ⟶ O₂) (x : X)
    (r : O₂.presheaf.stalk x) :
    comparisonInv φ x (CommRingCat.KaehlerDifferential.d r) =
      (derivation φ x).d r := sorry

/-- The forward stalk isomorphism sends the induced derivation of a stalk element to its
universal differential. -/
@[simp]
theorem iso_hom_d (φ : O₁ ⟶ O₂) (x : X) (r : O₂.presheaf.stalk x) :
    (iso φ x).hom ((derivation φ x).d r) =
      CommRingCat.KaehlerDifferential.d r := sorry

/-- The inverse comparison sends the differential of a germ to the germ of the sectionwise
universal differential. -/
@[stacks 08TE "inverse stalk comparison on germ differentials", simp]
theorem comparisonInv_d_germ (φ : O₁ ⟶ O₂) (x : X)
    (U : Opens X) (hx : x ∈ U) (r : O₂.presheaf.obj (op U)) :
    comparisonInv φ x
        (CommRingCat.KaehlerDifferential.d (O₂.presheaf.germ U x hx r)) =
      TopCat.Presheaf.germ
        (TopCat.Sheaf.relativeDifferentials φ).val.presheaf U x hx
        ((TopCat.Sheaf.relativeDifferential φ).d r) := sorry

/-- The forward comparison sends the germ of a sectionwise universal differential to the
universal differential of the corresponding germ. -/
@[stacks 08TE "forward stalk comparison on germ differentials", simp]
theorem comparison_germ_d (φ : O₁ ⟶ O₂) (x : X)
    (U : Opens X) (hx : x ∈ U) (r : O₂.presheaf.obj (op U)) :
    comparison φ x
        (TopCat.Presheaf.germ
          (TopCat.Sheaf.relativeDifferentials φ).val.presheaf U x hx
          ((TopCat.Sheaf.relativeDifferential φ).d r)) =
      CommRingCat.KaehlerDifferential.d
        (O₂.presheaf.germ U x hx r) := sorry

/-- The forward stalk isomorphism sends the germ of a universal differential to the universal
differential of the corresponding germ. -/
theorem iso_hom_germ_d (φ : O₁ ⟶ O₂) (x : X)
    (U : Opens X) (hx : x ∈ U) (r : O₂.presheaf.obj (op U)) :
    (iso φ x).hom
        (TopCat.Presheaf.germ
          (TopCat.Sheaf.relativeDifferentials φ).val.presheaf U x hx
          ((TopCat.Sheaf.relativeDifferential φ).d r)) =
      CommRingCat.KaehlerDifferential.d (O₂.presheaf.germ U x hx r) := sorry

end TopCat.Sheaf.RelativeDifferentials.Stalk
