/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import stacks_project.Chap96.Lemma_96_12_5_AssociatedModules
public import stacks_project.Chap96.Lemma_96_12_5_Comparison

/-!
# Lemma 96.12.5

Quasi-coherent modules on a category fibred in groupoids have colimits
agreeing with the associated Zariski, étale, and fppf module categories and
with locally quasi-coherent étale modules. Tensor products of quasi-coherent
modules computed in those associated module categories agree and remain
quasi-coherent. Internal Hom from a finite locally free quasi-coherent module,
computed in the Zariski, étale, or fppf module categories, agrees and remains
quasi-coherent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
  CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace QCoh

/-- Lemma 96.12.5 (1): the category `QCoh 𝒪_X` has colimits, and they agree with
colimits computed in `Mod(X_Zar, 𝒪_X)`, `Mod(X_étale, 𝒪_X)`, `Mod(𝒪_X)`, and
`LQCoh 𝒪_X`. -/
@[stacks 06WN]
instance closedUnderColimitsOfShape (X : GroupoidsOver S)
    (J : Type u) [Category.{u} J] :
    (quasiCoherentModuleProperty X).IsClosedUnderColimitsOfShape J :=
  sorry

/-- The inclusion `QCoh 𝒪_X → Mod(𝒪_X)` creates colimits of every
universe-compatible shape. -/
instance inclusion_createsColimitsOfShape (X : GroupoidsOver S)
    (J : Type u) [Category.{u} J] :
    CreatesColimitsOfShape J (quasiCoherentModuleProperty X).ι :=
  createsColimitsOfShapeFullSubcategoryInclusion J (quasiCoherentModuleProperty X)

/-- `QCoh 𝒪_X` has colimits of every universe-compatible shape. -/
instance hasColimitsOfShape (X : GroupoidsOver S)
    (J : Type u) [Category.{u} J] :
    HasColimitsOfShape J (QCoh X) :=
  sorry

/-- Colimits in `QCoh 𝒪_X` agree with colimits computed in `Mod(𝒪_X)`. -/
noncomputable def inclusion_colimitIso {X : GroupoidsOver S} {J : Type u}
    [Category.{u} J] (F : J ⥤ QCoh X)
    [HasColimit F] [HasColimit (F ⋙ (quasiCoherentModuleProperty X).ι)]
    [PreservesColimit F (quasiCoherentModuleProperty X).ι] :
    colimit (F ⋙ (quasiCoherentModuleProperty X).ι) ≅
      ((quasiCoherentModuleProperty X).ι).obj (colimit F) :=
  (preservesColimitIso (quasiCoherentModuleProperty X).ι F).symm

/-- Colimits in `QCoh 𝒪_X` agree with colimits computed in `Mod(X_Zar, 𝒪_X)`. -/
noncomputable def toAssociatedModules_colimitIso_zariski {X : GroupoidsOver S}
    {J : Type u} [Category.{u} J] (F : J ⥤ QCoh X)
    [HasColimit F] [HasColimit (F ⋙ toAssociatedModules X .zariski)]
    [PreservesColimit F (toAssociatedModules X .zariski)] :
    colimit (F ⋙ toAssociatedModules X .zariski) ≅
      (toAssociatedModules X .zariski).obj (colimit F) :=
  (preservesColimitIso (toAssociatedModules X .zariski) F).symm

/-- Colimits in `QCoh 𝒪_X` agree with colimits computed in `Mod(X_étale, 𝒪_X)`. -/
noncomputable def toEtaleModules_colimitIso {X : GroupoidsOver S} {J : Type u}
    [Category.{u} J] (F : J ⥤ QCoh X)
    [HasColimit F] [HasColimit (F ⋙ toEtaleModules X)]
    [PreservesColimit F (toEtaleModules X)] :
    colimit (F ⋙ toEtaleModules X) ≅ (toEtaleModules X).obj (colimit F) :=
  (preservesColimitIso (toEtaleModules X) F).symm

/-- Colimits in `QCoh 𝒪_X` agree with colimits computed in `LQCoh 𝒪_X`. -/
noncomputable def toLQCoh_colimitIso {X : GroupoidsOver S} {J : Type u}
    [Category.{u} J] (F : J ⥤ QCoh X)
    [HasColimit F] [HasColimit (F ⋙ toLQCoh X)]
    [PreservesColimit F (toLQCoh X)] :
    colimit (F ⋙ toLQCoh X) ≅ (toLQCoh X).obj (colimit F) :=
  (preservesColimitIso (toLQCoh X) F).symm

/-- Lemma 96.12.5 (2): the tensor product of two quasi-coherent `𝒪_X`-modules,
computed in `Mod(X_Zar, 𝒪_X)`, `Mod(X_étale, 𝒪_X)`, or `Mod(𝒪_X)`, agrees and
the common value is an object of `QCoh 𝒪_X`. -/
@[stacks 06WN]
noncomputable abbrev tensor {X : GroupoidsOver S} (F G : QCoh X) : QCoh X :=
  quasicoherentTensor F G

/-- The common tensor is computed using the module tensor on the commutative
fppf presentation, then transported back to fppf modules. -/
theorem tensor_obj {X : GroupoidsOver S} (F G : QCoh X) :
    (tensor F G).obj =
      (fromCommAssociatedModules X).obj
        (moduleTensorAssociated
          ((toCommAssociatedModules X .fppf).obj F)
          ((toCommAssociatedModules X .fppf).obj G)) :=
  rfl

/-- Tensor products computed in the associated Zariski module category agree
with the common quasi-coherent value. -/
instance tensorComparison_isIso_zariski {X : GroupoidsOver S} (F G : QCoh X) :
    IsIso (tensorComparison .zariski F G) :=
  sorry

/-- Tensor products computed in the associated étale module category agree with
the common quasi-coherent value. -/
instance tensorComparison_isIso_etale {X : GroupoidsOver S} (F G : QCoh X) :
    IsIso (tensorComparison .etale F G) :=
  sorry

/-- Tensor products computed in `Mod(𝒪_X)` agree with the common quasi-coherent
value. -/
instance tensorComparison_isIso_fppf {X : GroupoidsOver S} (F G : QCoh X) :
    IsIso (tensorComparison .fppf F G) :=
  sorry

/-- Lemma 96.12.5 (3): there is one quasi-coherent module with an evaluation
whose canonical comparison with the actual internal Hom is invertible in the
Zariski, étale and fppf module categories. The same object and evaluation are
used for all three topologies. -/
@[stacks 06WN]
theorem internalHom {X : GroupoidsOver S} (F G : QCoh X)
    [SheafOfModules.IsFiniteLocallyFree F.obj] :
    ∃ (H : QCoh X) (ev : quasicoherentTensor F H ⟶ G),
      ∀ τ ∈ [StandardTopology.zariski, .etale, .fppf],
        IsIso (internalHomComparison τ F G H ev) :=
  sorry

/-- Finite local freeness of a quasi-coherent module may equivalently be tested
in the Zariski, étale, or fppf topology. -/
theorem associatedFiniteLocallyFree_tfae {X : GroupoidsOver S} (F : QCoh X) :
    List.TFAE
      [SheafOfModules.IsFiniteLocallyFree F.obj,
        SheafOfModules.IsFiniteLocallyFree
          ((toAssociatedModules X .zariski).obj F),
        SheafOfModules.IsFiniteLocallyFree
          ((toAssociatedModules X .etale).obj F),
        SheafOfModules.IsFiniteLocallyFree
          ((toAssociatedModules X .fppf).obj F)] :=
  sorry

end QCoh

end AlgebraicGeometry.GroupoidsOver
