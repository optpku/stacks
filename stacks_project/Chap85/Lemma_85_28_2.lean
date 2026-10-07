module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicTopology.SimplicialObject.Cartesian
public import stacks_project.Chap85.Lemma_85_28_1_Pullback

/-!
# Lemma 85.28.2

Pushforward of a quasi-coherent module along a cartesian morphism of simplicial
schemes remains quasi-coherent on the Zariski ringed site of the target, when
cofaces of the target are flat and components of the morphism are quasi-compact
and quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- Lemma 85.28.2: let `f : V ⟶ U` be a cartesian morphism of simplicial schemes.
Assume the coface morphisms `U.δ j : U _⦋n+1⦌ ⟶ U _⦋n⦌` are flat and the
component morphisms `f.app (op ⦋n⦌) : V _⦋n⦌ ⟶ U _⦋n⦌` are quasi-compact and
quasi-separated. For a quasi-coherent module `G` on `zariskiRingedSite V`, the
pushforward `(zariskiRingedHom f).modulePushforward.obj G` is a quasi-coherent
module on `zariskiRingedSite U`. -/
@[stacks 07TJ]
instance modulePushforward_isQuasicoherent {V U : SimplicialObject Scheme.{u}}
    (f : V ⟶ U) [CategoryTheory.SimplicialObject.IsCartesian f]
    [∀ (n : ℕ) (j : Fin (n + 2)), Flat (U.δ j)]
    [∀ (n : ℕ), QuasiCompact (f.app (op ⦋n⦌))]
    [∀ (n : ℕ), QuasiSeparated (f.app (op ⦋n⦌))]
    (G : SheafOfModules.{u} (zariskiRingedSite V).structureSheaf)
    [G.IsQuasicoherent] :
    ((zariskiRingedHom f).modulePushforward.{u}.obj G).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.SimplicialObject
