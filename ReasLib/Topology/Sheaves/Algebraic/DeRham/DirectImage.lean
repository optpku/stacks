/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaves.Algebraic.DeRham
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Direct-image comparison for relative de Rham complexes

For a continuous map `f : X ⟶ Y`, relative forms of the direct-image ring sheaves map
canonically to the direct image of the relative form sheaves.  The construction is induced by the
identity map on every section module and the module-sheafification adjunction.
-/

@[expose] public section

open CategoryTheory ComplexShape TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace TopCat.Sheaf.DeRham.DirectImage

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable {O₁ O₂ : X.Sheaf CommRingCat.{u}}

/-- Direct image of a commutative ring sheaf. -/
abbrev ring (O : X.Sheaf CommRingCat.{u}) : Y.Sheaf CommRingCat.{u} :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} f).obj O

/-- Direct image of a morphism of commutative ring sheaves. -/
abbrev ringMap (φ : O₁ ⟶ O₂) : ring f O₁ ⟶ ring f O₂ :=
  (TopCat.Sheaf.pushforward CommRingCat.{u} f).map φ

/-- The underlying ring-sheaf map identifying the ring sheaf of a direct image with the direct
image of the underlying ring sheaf. -/
abbrev structureMap (O : X.Sheaf CommRingCat.{u}) :=
  TopCat.Sheaf.commRingSheafPushforwardId f O

/-- Direct image of module sheaves along the canonical underlying-ring comparison. -/
abbrev modules (O : X.Sheaf CommRingCat.{u}) :=
  SheafOfModules.pushforward (structureMap f O)

/-- Direct image of module sheaves is additive. -/
instance modules_additive (O : X.Sheaf CommRingCat.{u}) : (modules f O).Additive := sorry

/-- Direct image on cochain complexes of module sheaves. -/
abbrev complexes (O : X.Sheaf CommRingCat.{u}) :=
  (modules f O).mapHomologicalComplex (up ℕ)

/-- The presheaf term of the de Rham complex of the direct-image ring morphism. -/
abbrev source (φ : O₁ ⟶ O₂) (p : ℕ) :=
  PresheafOfModules.DeRham.term (ringMap f φ).hom p

variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/-- The presheaf underlying the direct image of a sheafified relative de Rham term. -/
abbrev target (φ : O₁ ⟶ O₂) (p : ℕ) :=
  ((modules f O₁).obj (TopCat.Sheaf.DeRham.term φ p)).val

/-- The canonical sectionwise comparison from direct-image relative forms to direct images of
relative forms. -/
noncomputable def presheafMapApp (φ : O₁ ⟶ O₂) (p : ℕ) (U : (Opens Y)ᵒᵖ) :
    (source f φ p).obj U ⟶ (target f φ p).obj U :=
  (SheafOfModules.RingedSite.DeRham.termUnit φ p).app ((Opens.map f).op.obj U)

/-- The sectionwise comparisons from direct-image relative forms to direct images of relative
forms commute with restriction maps. -/
theorem presheafMap_naturality (φ : O₁ ⟶ O₂) (p : ℕ)
    {U V : (Opens Y)ᵒᵖ} (a : U ⟶ V) :
    (source f φ p).map a ≫
        (ModuleCat.restrictScalars
          (((TopCat.Sheaf.ringSheafOfComm (ring f O₁)).obj.map a).hom)).map
            (presheafMapApp f φ p V) =
      presheafMapApp f φ p U ≫ (target f φ p).map a := sorry

/-- The sectionwise identity morphism from the de Rham term of direct-image ring presheaves to
the presheaf underlying the direct image term. -/
@[stacks 0FKQ "(2), direct-image presheaf comparison"]
def presheafMap (φ : O₁ ⟶ O₂) (p : ℕ) : source f φ p ⟶ target f φ p where
  app U := presheafMapApp f φ p U
  naturality a := presheafMap_naturality f φ p a

variable [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat]
variable [(Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat]

/-- Sheafification of the sectionwise direct-image comparison. -/
noncomputable def sheafifiedMap (φ : O₁ ⟶ O₂) (p : ℕ) :
    (moduleSheafification (ring f O₁)).obj (source f φ p) ⟶
      (modules f O₁).obj (TopCat.Sheaf.DeRham.term φ p) :=
  ((moduleSheafificationAdjunction (ring f O₁)).homEquiv
    (source f φ p) ((modules f O₁).obj (TopCat.Sheaf.DeRham.term φ p))).symm
      (presheafMap f φ p ≫
        (valRestrictionIso (ring f O₁)
          ((modules f O₁).obj (TopCat.Sheaf.DeRham.term φ p))).hom)

/-- The degree-`p` comparison from the de Rham complex of direct-image ring sheaves to the direct
image of the original de Rham term. -/
@[stacks 0FKQ "(2), direct-image term comparison"]
noncomputable def mapApp (φ : O₁ ⟶ O₂) (p : ℕ) :
    TopCat.Sheaf.DeRham.term (ringMap f φ) p ⟶
      (modules f O₁).obj (TopCat.Sheaf.DeRham.term φ p) :=
  (ModuleSheafification.restrictionComponentIso (ringMap f φ)
      (PresheafOfModules.DeRham.form (ringMap f φ).hom p)).inv ≫
    sheafifiedMap f φ p

/-- The degreewise direct-image comparisons commute with the de Rham differentials. -/
theorem mapApp_comm (φ : O₁ ⟶ O₂) (i j : ℕ) (hij : (up ℕ).Rel i j) :
    mapApp f φ i ≫ ((complexes f O₁).obj (TopCat.Sheaf.DeRham.complex φ)).d i j =
      (TopCat.Sheaf.DeRham.complex (ringMap f φ)).d i j ≫ mapApp f φ j := sorry

/-- The canonical map from the relative de Rham complex of direct-image ring sheaves to the
direct image of the relative de Rham complex. -/
@[stacks 0FKQ "(2), direct-image comparison"]
noncomputable def map (φ : O₁ ⟶ O₂) :
    TopCat.Sheaf.DeRham.complex (ringMap f φ) ⟶
      (complexes f O₁).obj (TopCat.Sheaf.DeRham.complex φ) where
  f p := mapApp f φ p
  comm' i j hij := mapApp_comm f φ i j hij

/-- The degree-`p` component of the direct-image comparison is `mapApp`. -/
theorem map_f (φ : O₁ ⟶ O₂) (p : ℕ) :
    (map f φ).f p = mapApp f φ p := sorry

end TopCat.Sheaf.DeRham.DirectImage
