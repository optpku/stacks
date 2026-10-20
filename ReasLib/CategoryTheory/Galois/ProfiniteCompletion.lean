module

public import ReasLib.CategoryTheory.Action.Finite.Forget
public import ReasLib.CategoryTheory.Functor.AutTopology
public import ReasLib.Topology.Category.ProfiniteGrp.Completion
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.Topology.Category.FinTopCat

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

universe u

namespace CategoryTheory.DiscreteContAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The finite discrete continuous `G`-set associated to an open finite-index normal subgroup. -/
def ofOpenFiniteIndexNormalSubgroup
    (H : OpenFiniteIndexNormalSubgroup G) : DiscreteContAction FintypeCat.{u} G :=
  ⟨⟨Action.FintypeCat.ofMulAction G (FintypeCat.of (G ⧸ H.obj.toSubgroup)), sorry⟩, sorry⟩

/-- Evaluation of a natural automorphism of `forgetFinite` on the distinguished coset of an
open finite-index normal subgroup. -/
def autForget_eval (σ : Aut (forgetFinite G)) (H : OpenFiniteIndexNormalSubgroup G) :
    (TopologicalProfiniteCompletion.diagram G).obj H :=
  (σ.hom.app (ofOpenFiniteIndexNormalSubgroup G H)) (QuotientGroup.mk (1 : G))

/-- The compatible family of cosets associated to a natural automorphism of `forgetFinite`. -/
def autForget_toLimitFun (σ : Aut (forgetFinite G)) :
    TopologicalProfiniteCompletion.completion G :=
  ⟨fun H ↦ autForget_eval G σ H, sorry⟩

/-- The kernel of the permutation representation of `G` on a finite discrete continuous `G`-set. -/
def actionKernel (X : DiscreteContAction FintypeCat.{u} G) : Subgroup G :=
  (MulAction.toPermHom G X.obj.obj.V).ker

/-- The kernel of a permutation representation is normal. -/
instance actionKernel_normal (X : DiscreteContAction FintypeCat.{u} G) :
    (actionKernel G X).Normal :=
  inferInstanceAs ((MulAction.toPermHom G X.obj.obj.V).ker.Normal)

/-- The kernel of the permutation representation, as an open finite-index normal subgroup. -/
def actionKernelSubgroup (X : DiscreteContAction FintypeCat.{u} G) :
    OpenFiniteIndexNormalSubgroup G :=
  ⟨{ toOpenSubgroup := { actionKernel G X with isOpen' := sorry } }, sorry⟩

/-- The permutation of a finite discrete continuous `G`-set induced by a compatible family of
finite quotients. -/
def autForget_ofLimitApp
    (x : TopologicalProfiniteCompletion.completion G)
    (X : DiscreteContAction FintypeCat.{u} G) :
    (forgetFinite G).obj X ⟶ (forgetFinite G).obj X :=
  TypeCat.ofHom fun y ↦
    (QuotientGroup.lift (actionKernel G X)
      (MulAction.toPermHom G X.obj.obj.V) (fun _ h ↦ h)
      (x.val (actionKernelSubgroup G X))) y

/-- The inverse permutation induced by a compatible family of finite quotients. -/
def autForget_ofLimitAppInv
    (x : TopologicalProfiniteCompletion.completion G)
    (X : DiscreteContAction FintypeCat.{u} G) :
    (forgetFinite G).obj X ⟶ (forgetFinite G).obj X :=
  TypeCat.ofHom fun y ↦
    (QuotientGroup.lift (actionKernel G X)
      (MulAction.toPermHom G X.obj.obj.V) (fun _ h ↦ h)
      (x.val (actionKernelSubgroup G X))).symm y

/-- The automorphism of `forgetFinite` associated to a point of the topology-sensitive
profinite completion. -/
def autForget_ofLimitFun (x : TopologicalProfiniteCompletion.completion G) :
    Aut (forgetFinite G) :=
  { hom :=
      { app := autForget_ofLimitApp G x
        naturality := sorry }
    inv :=
      { app := autForget_ofLimitAppInv G x
        naturality := sorry }
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The automorphism group of the finite continuous `G`-set forgetful functor is the
topology-sensitive profinite completion of `G`. -/
noncomputable def autForget_profiniteCompletionIso :
    Aut (forgetFinite G) ≃ₜ* TopologicalProfiniteCompletion.completion G where
  toFun := autForget_toLimitFun G
  invFun := autForget_ofLimitFun G
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

end CategoryTheory.DiscreteContAction
