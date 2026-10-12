/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CardinalGeneration.Small
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.CardinalGeneration

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Scheme.QCoh

noncomputable section

universe u

namespace AlgebraicGeometry
namespace GroupoidScheme
namespace QCoh

/-- A subobject is invariant when the equivariance action restricts to its two pullbacks. -/
def IsInvariant {S : Scheme.{u}} (G : GroupoidScheme S)
    {A : G.QCoh} (B : Subobject A.obj) : Prop :=
  ∃ action : (Scheme.QCoh.pullback G.t.left).obj (B : Scheme.QCoh G.U.left) ⟶
      (Scheme.QCoh.pullback G.s.left).obj (B : Scheme.QCoh G.U.left),
    CommSq action ((Scheme.QCoh.pullback G.t.left).map B.arrow)
      ((Scheme.QCoh.pullback G.s.left).map B.arrow) A.action

/-- Invariance means that the equivariance action restricts to a commutative square on the
chosen subobject. -/
theorem isInvariant_iff {S : Scheme.{u}} (G : GroupoidScheme S)
    {A : G.QCoh} (B : Subobject A.obj) :
    IsInvariant G B ↔
      ∃ action : (Scheme.QCoh.pullback G.t.left).obj (B : Scheme.QCoh G.U.left) ⟶
          (Scheme.QCoh.pullback G.s.left).obj (B : Scheme.QCoh G.U.left),
        CommSq action ((Scheme.QCoh.pullback G.t.left).map B.arrow)
          ((Scheme.QCoh.pullback G.s.left).map B.arrow) A.action :=
  Iff.rfl

/-- The invariant subobjects whose underlying quasi-coherent modules are `κ`-generated. -/
def kappaGeneratedSubobjects {S : Scheme.{u}} (G : GroupoidScheme S)
    (κ : Cardinal.{u}) (A : G.QCoh) : Set (Subobject A.obj) :=
  { B | ((B : Scheme.QCoh G.U.left).obj).IsKappaGenerated κ ∧ IsInvariant G B }

/-- Membership in `kappaGeneratedSubobjects` means generation by at most `κ` elements locally
and invariance under the equivariance action. -/
@[simp] theorem mem_kappaGeneratedSubobjects {S : Scheme.{u}} (G : GroupoidScheme S)
    (κ : Cardinal.{u}) (A : G.QCoh) (B : Subobject A.obj) :
    B ∈ kappaGeneratedSubobjects G κ A ↔
      ((B : Scheme.QCoh G.U.left).obj).IsKappaGenerated κ ∧ IsInvariant G B :=
  Iff.rfl

/-- Enlarging the cardinal bound preserves membership in the bounded invariant family. -/
lemma mem_kappaGeneratedSubobjects_of_le {S : Scheme.{u}} (G : GroupoidScheme S)
    {κ κ' : Cardinal.{u}} {A : G.QCoh} {B : Subobject A.obj}
    (hκ : κ ≤ κ') (hB : B ∈ kappaGeneratedSubobjects G κ A) :
    B ∈ kappaGeneratedSubobjects G κ' A := by
  rcases hB with ⟨⟨q, hq⟩, hBinv⟩
  exact ⟨⟨q, fun i ↦ (hq i).trans hκ⟩, hBinv⟩

/-- The top subobject is invariant under the ambient equivariance action. -/
lemma isInvariant_top {S : Scheme.{u}} (G : GroupoidScheme S) (A : G.QCoh) :
    IsInvariant G (⊤ : Subobject A.obj) := by
  let e : ((⊤ : Subobject A.obj) : Scheme.QCoh G.U.left) ≅ A.obj :=
    asIso ((⊤ : Subobject A.obj).arrow)
  refine ⟨(Scheme.QCoh.pullback G.t.left).map e.hom ≫
      A.action ≫ (Scheme.QCoh.pullback G.s.left).map e.inv, ?_⟩
  dsimp [e]
  simp [Category.assoc]

/-- If an equivariant object is `κ`-generated, its top subobject belongs to the bounded
invariant family. -/
lemma top_mem_kappaGeneratedSubobjects_of_isKappaGenerated {S : Scheme.{u}}
    (G : GroupoidScheme S) (κ : Cardinal.{u}) (A : G.QCoh)
    (hA : A.obj.obj.IsKappaGenerated κ) :
    (⊤ : Subobject A.obj) ∈ kappaGeneratedSubobjects G κ A := by
  let e : ((⊤ : Subobject A.obj) : Scheme.QCoh G.U.left) ≅ A.obj :=
    asIso ((⊤ : Subobject A.obj).arrow)
  let e' := (Scheme.QCoh.inclusion G.U.left).mapIso e
  refine ⟨?_, isInvariant_top G A⟩
  exact (SheafOfModules.isKappaGenerated_iff_of_iso e' κ).mpr hA

/-- For a groupoid scheme with flat source and target, one cardinal uniformly bounds a
directed family of invariant quasi-coherent subobjects whose least upper bound is top. -/
theorem exists_cardinal_kappaGeneratedSubobjects_isDirectedColimit
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [Flat G.s.left] [Flat G.t.left] :
    ∃ κ : Cardinal.{u}, ∀ A : G.QCoh,
      DirectedOn (· ≤ ·) (kappaGeneratedSubobjects G κ A) ∧
        IsLUB (kappaGeneratedSubobjects G κ A) (⊤ : Subobject A.obj) := sorry

end QCoh
end GroupoidScheme
end AlgebraicGeometry
