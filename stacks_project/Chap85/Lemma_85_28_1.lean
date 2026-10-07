module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_28_1_Ringed
public import stacks_project.Chap85.Lemma_85_28_1_Pullback

/-!
# Lemma 85.28.1

Pullback of quasi-coherent modules along a morphism of simplicial schemes remains
quasi-coherent on the Zariski ringed site of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- Lemma 85.28.1: let `f : V ⟶ U` be a morphism of simplicial schemes. Given a
quasi-coherent module `F` on `zariskiRingedSite U`, the pullback
`(zariskiRingedHom f).modulePullback.obj F` is a quasi-coherent module on
`zariskiRingedSite V`. -/
@[stacks 07TI]
instance modulePullback_isQuasicoherent {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    (F : SheafOfModules.{u} (zariskiRingedSite U).structureSheaf)
    [F.IsQuasicoherent] :
    ((zariskiRingedHom f).modulePullback.obj F).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.SimplicialObject
