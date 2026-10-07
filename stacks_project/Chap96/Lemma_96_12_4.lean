module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import stacks_project.Chap96.Lemma_96_12_4_EtaleModules
public import stacks_project.Chap96.Lemma_96_12_4_LQCoh

/-!
# Lemma 96.12.4

Locally quasi-coherent étale modules on a category fibred in groupoids have
colimits created in the ambient étale module category, form a weak Serre class
(so the inclusion is exact), and are closed under tensor and under internal Hom
from a finitely presented étale module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed CategoryTheory.ObjectProperty
open AlgebraicGeometry
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

namespace LQCoh

/-- Lemma 96.12.4 (1): the category `LQCoh 𝒪_X` has colimits, and they agree with
colimits computed in `Mod(X_étale, 𝒪_X)`. -/
@[stacks 06WM]
instance closedUnderColimitsOfShape (X : GroupoidsOver S)
    (J : Type v) [Category.{w} J] :
    (locallyQuasiCoherent X).IsClosedUnderColimitsOfShape J := sorry

/-- The inclusion `LQCoh 𝒪_X → Mod(X_étale, 𝒪_X)` creates colimits of every
universe-compatible shape. -/
instance inclusion_createsColimitsOfShape (X : GroupoidsOver S)
    (J : Type v) [Category.{w} J] :
    CreatesColimitsOfShape J (LQCoh.inclusion X) :=
  createsColimitsOfShapeFullSubcategoryInclusion J (locallyQuasiCoherent X)

/-- `LQCoh 𝒪_X` has colimits of every universe-compatible shape. -/
instance hasColimitsOfShape (X : GroupoidsOver S)
    (J : Type v) [Category.{w} J] :
    HasColimitsOfShape J (LQCoh X) := sorry

/-- Colimits in `LQCoh 𝒪_X` agree with colimits computed in `Mod(X_étale, 𝒪_X)`. -/
noncomputable def inclusion_colimitIso {X : GroupoidsOver S} {J : Type v} [Category.{w} J]
    (F : J ⥤ LQCoh X) [HasColimit F] [HasColimit (F ⋙ LQCoh.inclusion X)]
    [PreservesColimit F (LQCoh.inclusion X)] :
    colimit (F ⋙ LQCoh.inclusion X) ≅ (LQCoh.inclusion X).obj (colimit F) :=
  (preservesColimitIso (LQCoh.inclusion X) F).symm

/-- `inclusion_colimitIso` is the inverse of the canonical `preservesColimitIso`. -/
theorem inclusion_colimitIso_eq {X : GroupoidsOver S} {J : Type v} [Category.{w} J]
    (F : J ⥤ LQCoh X) [HasColimit F] [HasColimit (F ⋙ LQCoh.inclusion X)]
    [PreservesColimit F (LQCoh.inclusion X)] :
    inclusion_colimitIso F = (preservesColimitIso (LQCoh.inclusion X) F).symm := sorry

/-- Lemma 96.12.4 (2): `LQCoh 𝒪_X` is abelian, with kernels and cokernels computed
in `Mod(X_étale, 𝒪_X)`; equivalently, the inclusion functor is exact. -/
@[stacks 06WM]
instance isWeakSerreClass (X : GroupoidsOver S) :
    (locallyQuasiCoherent X).IsWeakSerreClass := sorry

/-- The inclusion `LQCoh 𝒪_X → Mod(X_étale, 𝒪_X)` is exact. -/
theorem inclusion_exact (X : GroupoidsOver S) :
    exactFunctor (LQCoh X) (etaleModules X) (LQCoh.inclusion X) := sorry

end LQCoh

/-- Lemma 96.12.4 (3): in a short exact sequence of étale `𝒪_X`-modules, if two of
the three terms are locally quasi-coherent then so is the third. -/
@[stacks 06WM]
theorem isLocallyQuasiCoherent_of_shortExact_two_out_of_three
    {X : GroupoidsOver S} {sc : ShortComplex (etaleModules X)} (hsc : sc.ShortExact)
    (h : (locallyQuasiCoherent X sc.X₁ ∧ locallyQuasiCoherent X sc.X₂) ∨
        (locallyQuasiCoherent X sc.X₁ ∧ locallyQuasiCoherent X sc.X₃) ∨
        (locallyQuasiCoherent X sc.X₂ ∧ locallyQuasiCoherent X sc.X₃)) :
    locallyQuasiCoherent X sc.X₁ ∧ locallyQuasiCoherent X sc.X₂ ∧
      locallyQuasiCoherent X sc.X₃ := sorry

/-- Lemma 96.12.4 (4): the tensor product of two locally quasi-coherent étale
`𝒪_X`-modules, computed in `Mod(X_étale, 𝒪_X)`, is locally quasi-coherent. -/
@[stacks 06WM]
instance isLocallyQuasiCoherent_tensor {X : GroupoidsOver S}
    (F G : etaleModules X) [IsLocallyQuasiCoherent F] [IsLocallyQuasiCoherent G] :
    IsLocallyQuasiCoherent (moduleTensorEtale F G) := sorry

/-- Lemma 96.12.4 (5): internal Hom from a finitely presented étale module into a
locally quasi-coherent étale module, computed in `Mod(X_étale, 𝒪_X)`, is locally
quasi-coherent. -/
@[stacks 06WM]
instance isLocallyQuasiCoherent_internalHom {X : GroupoidsOver S}
    (F G : RingedSite.ModuleCat.{u + 1} (commEtaleRingedSiteLift X))
    [F.IsFinitePresentation] [IsLocallyQuasiCoherentLift F]
    [IsLocallyQuasiCoherentLift G] :
    IsLocallyQuasiCoherentLift ((ihom F).obj G) := sorry

end AlgebraicGeometry.GroupoidsOver
