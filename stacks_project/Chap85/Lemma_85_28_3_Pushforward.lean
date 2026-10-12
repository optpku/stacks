/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap85.Lemma_85_28_2
public import stacks_project.Chap85.Lemma_85_28_4_QCoh

/-!
# Quasi-coherent pushforward along a cartesian morphism of simplicial schemes

Restriction of module pushforward along `zariskiRingedHom f` to quasi-coherent
modules, under cartesianness, flat cofaces, and quasi-compact quasi-separated
components.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty Opposite
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

namespace QCoh

namespace pushforward

/-- Pushforward of module sheaves along a cartesian morphism of simplicial schemes
carries quasi-coherent modules to quasi-coherent modules, when cofaces of the
target are flat and components of the morphism are quasi-compact and
quasi-separated. -/
theorem mapsTo {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    [CategoryTheory.SimplicialObject.IsCartesian f]
    [∀ (n : ℕ) (j : Fin (n + 2)), Flat (U.δ j)]
    [∀ (n : ℕ), QuasiCompact (f.app (op ⦋n⦌))]
    [∀ (n : ℕ), QuasiSeparated (f.app (op ⦋n⦌))] :
    quasiCoherentModuleProperty V ≤
      (quasiCoherentModuleProperty U).inverseImage
        (zariskiRingedHom f).modulePushforward.{u} :=
  sorry

end pushforward

/-- Pushforward of quasi-coherent modules along a cartesian morphism of simplicial
schemes with flat cofaces and quasi-compact quasi-separated components. -/
noncomputable def pushforward {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    [CategoryTheory.SimplicialObject.IsCartesian f]
    [∀ (n : ℕ) (j : Fin (n + 2)), Flat (U.δ j)]
    [∀ (n : ℕ), QuasiCompact (f.app (op ⦋n⦌))]
    [∀ (n : ℕ), QuasiSeparated (f.app (op ⦋n⦌))] :
    QCoh V ⥤ QCoh U :=
  FullSubcategory.restrict (zariskiRingedHom f).modulePushforward.{u}
    (pushforward.mapsTo f)

/-- The underlying module sheaf of a pushed-forward quasi-coherent module is the
usual module pushforward. -/
theorem pushforward_obj {V U : SimplicialObject Scheme.{u}} (f : V ⟶ U)
    [CategoryTheory.SimplicialObject.IsCartesian f]
    [∀ (n : ℕ) (j : Fin (n + 2)), Flat (U.δ j)]
    [∀ (n : ℕ), QuasiCompact (f.app (op ⦋n⦌))]
    [∀ (n : ℕ), QuasiSeparated (f.app (op ⦋n⦌))]
    (G : QCoh V) :
    ((pushforward f).obj G).obj =
      (zariskiRingedHom f).modulePushforward.{u}.obj G.obj :=
  sorry

/-- Forgetting quasi-coherence after restricted pushforward recovers ambient
module-sheaf pushforward. -/
noncomputable def pushforward.inclusionIso {V U : SimplicialObject Scheme.{u}}
    (f : V ⟶ U)
    [CategoryTheory.SimplicialObject.IsCartesian f]
    [∀ (n : ℕ) (j : Fin (n + 2)), Flat (U.δ j)]
    [∀ (n : ℕ), QuasiCompact (f.app (op ⦋n⦌))]
    [∀ (n : ℕ), QuasiSeparated (f.app (op ⦋n⦌))] :
    pushforward f ⋙ inclusion U ≅
      inclusion V ⋙ (zariskiRingedHom f).modulePushforward.{u} :=
  FullSubcategory.restrict.compιIso
    (zariskiRingedHom f).modulePushforward.{u} (pushforward.mapsTo f)

end QCoh

end AlgebraicGeometry.SimplicialObject
