/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap78.Lemma_78_12_3_QCoh

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory SheafOfModules

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh

/-- Lemma 78.13.4: Let `B → S` be as in Section 78.3. Let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over `B`. Assume that `U` and `R` are Noetherian and
that `s`, `t` are flat, quasi-compact, and quasi-separated. Then every quasi-coherent
module `(F, α)` on `(U, R, s, t, c)` is a filtered colimit of coherent modules, where
coherent means that the underlying `𝒪_U`-module is coherent. -/
@[stacks 0GPS]
theorem isCoherent_ind {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.IsNoetherian G.U.left] [AlgebraicSpace.IsNoetherian G.R.left]
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
    [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left]
    [AlgebraicSpace.QuasiSeparated G.s.left] [AlgebraicSpace.QuasiSeparated G.t.left]
    (F : G.QCoh) :
    ObjectProperty.ind.{u} (fun E : G.QCoh ↦ IsCoherent E.obj.obj) F := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
