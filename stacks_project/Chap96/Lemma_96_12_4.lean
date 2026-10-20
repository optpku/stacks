module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent.Properties
import StacksCheckRecall

/-!
# Locally quasi-coherent étale modules

The five closure properties and their canonical categorical consequences.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed
  CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver
open SheafOfModules.RingedSite (ringedSiteModuleCategory)

noncomputable section

universe u v w

variable {S : Scheme.{u}}

/- Lemma 96.12.4 (1): locally quasi-coherent modules are closed under ambient colimits. -/
@[stacks 06WM] #check (AlgebraicGeometry.GroupoidsOver.LQCoh.closedUnderColimitsOfShape :
  ∀ (X : GroupoidsOver S) (J : Type v) [Category.{w} J],
    (locallyQuasiCoherent X).IsClosedUnderColimitsOfShape J)

section Colimits

variable (X : GroupoidsOver S) (J : Type v) [Category.{w} J]
  [HasColimitsOfShape J AddCommGrpCat.{u}]

#check (CategoryTheory.Limits.createsColimitsOfShapeFullSubcategoryInclusion
  J (AlgebraicGeometry.GroupoidsOver.locallyQuasiCoherent X) :
  CreatesColimitsOfShape J (LQCoh.inclusion X))

#check (CategoryTheory.Limits.hasColimitsOfShape_of_closedUnderColimits
  J (AlgebraicGeometry.GroupoidsOver.locallyQuasiCoherent X) :
  HasColimitsOfShape J (LQCoh X))

end Colimits

section ColimitComparison

variable {X : GroupoidsOver S} {J : Type v} [Category.{w} J]
  (F : J ⥤ LQCoh X) [HasColimit F] [HasColimit (F ⋙ LQCoh.inclusion X)]
  [PreservesColimit F (LQCoh.inclusion X)]

#check (CategoryTheory.preservesColimitIso (LQCoh.inclusion X) F :
  (LQCoh.inclusion X).obj (colimit F) ≅ colimit (F ⋙ LQCoh.inclusion X))

end ColimitComparison

/- Lemma 96.12.4 (2): locally quasi-coherent modules form an abelian full subcategory,
with ambient kernels and cokernels and exact inclusion. -/
@[stacks 06WM] #check (AlgebraicGeometry.GroupoidsOver.LQCoh.isWeakSerreClass :
  ∀ (X : GroupoidsOver S), (locallyQuasiCoherent X).IsWeakSerreClass)

variable (X : GroupoidsOver S)

#check (CategoryTheory.ObjectProperty.IsWeakSerreClass.Inclusion.isExact
  (AlgebraicGeometry.GroupoidsOver.locallyQuasiCoherent X) :
  exactFunctor (LQCoh X) (etaleModules X) (LQCoh.inclusion X))

/- Lemma 96.12.4 (3): in a short exact sequence, local quasi-coherence satisfies
all three two-out-of-three implications. -/
@[stacks 06WM] #check
  (AlgebraicGeometry.GroupoidsOver.isLocallyQuasiCoherent_of_shortExact_two_out_of_three :
    ∀ {X : GroupoidsOver S} {sc : ShortComplex (etaleModules X)}, sc.ShortExact →
      ((locallyQuasiCoherent X sc.X₁ ∧ locallyQuasiCoherent X sc.X₂) ∨
        (locallyQuasiCoherent X sc.X₁ ∧ locallyQuasiCoherent X sc.X₃) ∨
        (locallyQuasiCoherent X sc.X₂ ∧ locallyQuasiCoherent X sc.X₃)) →
      locallyQuasiCoherent X sc.X₁ ∧ locallyQuasiCoherent X sc.X₂ ∧
        locallyQuasiCoherent X sc.X₃)

/- Lemma 96.12.4 (4): the ambient tensor product preserves local quasi-coherence. -/
@[stacks 06WM] #check (AlgebraicGeometry.GroupoidsOver.isLocallyQuasiCoherent_tensor :
  ∀ {X : GroupoidsOver S} (F G : etaleModules X)
    [IsLocallyQuasiCoherent F] [IsLocallyQuasiCoherent G],
    IsLocallyQuasiCoherent (moduleTensorEtale F G))

/- Lemma 96.12.4 (5): internal Hom from a finitely presented locally quasi-coherent
module to a locally quasi-coherent module is locally quasi-coherent. -/
@[stacks 06WM] #check (AlgebraicGeometry.GroupoidsOver.isLocallyQuasiCoherent_internalHom :
  ∀ {X : GroupoidsOver S}
    (F G : ringedSiteModuleCategory.{u + 1, u, u + 1, u + 1}
      X.etaleTopology (commEtaleStructureSheafLift X))
    [F.IsFinitePresentation] [IsLocallyQuasiCoherentLift F]
    [IsLocallyQuasiCoherentLift G],
    IsLocallyQuasiCoherentLift ((ihom F).obj G))
