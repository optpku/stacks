/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteTensorAction
public import stacks_project.Chap64.Proposition_64_29_3_CompletedGroupRingAlgebra

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open scoped MonoidAlgebra TensorProduct

noncomputable section

universe u

namespace CompactRepresentation

variable (Λ G : Type u) [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- The actual completed-ring action at each finite continuous quotient uses
its actual finite action kernel, never a kernel of an infinite discrete action. -/
def finiteCompletedAction (M : Cat Λ G) (U : OpenInvariantSubmodule Λ G M) :
    completedGroupRing Λ G →+* Module.End Λ (OpenInvariantSubmodule.quotient U) :=
  (OpenInvariantSubmodule.groupAlgebraAction U).toRingHom.comp
    (completedGroupRing.π Λ G (OpenInvariantSubmodule.normalKernel U))

/-- The tensor stage is balanced for the specified finite-stage action of the
actual completed ring; Λ is its right trivial module via augmentation. -/
theorem finiteCompletedTensor_balanced (M : Cat Λ G) (U : OpenInvariantSubmodule Λ G M)
    (r : completedGroupRing Λ G) (a : Λ) (m : OpenInvariantSubmodule.quotient U) :
    (OpenInvariantSubmodule.tensorRelations U).mkQ
      (a ⊗ₜ[Λ] finiteCompletedAction Λ G M U r m) =
    (OpenInvariantSubmodule.tensorRelations U).mkQ
      ((completedGroupRing.augmentation Λ G r * a) ⊗ₜ[Λ] m) := by sorry

/-- Functorial completed tensor, using the specified finite-projection
comparison with the actual compact quotient. -/
def completedTensorFunctor : Cat Λ G ⥤ CompactModule Λ where
  obj := completedTrivialTensor Λ G
  map {M N} f := (completedTensorComparison Λ G M).inv ≫
    coinvariantsMap Λ G f ≫ (completedTensorComparison Λ G N).hom
  map_id := by sorry
  map_comp := by sorry

instance : (completedTensorFunctor Λ G).Additive := by constructor; intros; sorry

/-- The natural comparison has the actual finite-stage projection formula. -/
def completedTensorFunctorIso : coinvariantsFunctor Λ G ≅ completedTensorFunctor Λ G :=
  NatIso.ofComponents (completedTensorComparison Λ G) (by sorry)

/-- Apply the independently defined finite-stage completed tensor functor to
the compact projective chain. -/
def completedTensorChain {M : DiscreteModuleCat Λ G} (I : InjectiveResolution M) :=
  ((completedTensorFunctor Λ G).mapHomologicalComplex (ComplexShape.down ℕ)).obj (dualChain Λ G I)

def completedTensorChainComparison {M : DiscreteModuleCat Λ G} (I : InjectiveResolution M) :
    coinvariantChain Λ G I ≅ completedTensorChain Λ G I :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ completedTensorComparison Λ G (dual Λ G (I.cocomplex.X n))) (by sorry)

/-- Compactly derived completed tensor, not algebraic ModuleCat Tor. -/
def completedTensorHomology (i : ℕ) : Cat Λ G ⥤ CompactModule Λ :=
  (completedTensorFunctor Λ G).leftDerived i

/-- Derive the specified natural comparison, keeping its actual maps. -/
def continuousHomologyCompletedTensorIso (i : ℕ) :
    continuousHomology Λ G i ≅ completedTensorHomology Λ G i where
  hom := NatTrans.leftDerived (completedTensorFunctorIso Λ G).hom i
  inv := NatTrans.leftDerived (completedTensorFunctorIso Λ G).inv i
  hom_inv_id := by sorry
  inv_hom_id := by sorry

/-- The character comparison factors through the actual compact tensor
resolution and the actual restriction/evaluation chain comparison. -/
def completedTensorCharacterIso {M : DiscreteModuleCat Λ G}
    (I : InjectiveResolution M) (i : ℕ) :
    (CompactModule.forget Λ).obj ((completedTensorHomology Λ G i).obj (dual Λ G M)) ≅
      ModuleCat.of Λ (CharacterModule ((AmbientDiscreteCohomology.cohomology Λ G i).obj M)) :=
  (CompactModule.forget Λ).mapIso ((continuousHomologyCompletedTensorIso Λ G i).app (dual Λ G M)).symm ≪≫
    derivedHomologyCharacterIso Λ G I i

end CompactRepresentation
