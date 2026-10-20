module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent.Coherent

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory SheafOfModules

universe u

/- Lemma 78.13.4: Let `B → S` be as in Section 78.3. Let `(U, R, s, t, c)` be a
groupoid in algebraic spaces over `B`. Assume that `U` and `R` are Noetherian and
that `s`, `t` are flat, quasi-compact, and quasi-separated. Then every quasi-coherent
module `(F, α)` on `(U, R, s, t, c)` is a filtered colimit of coherent modules, where
coherent means that the underlying `𝒪_U`-module is coherent. -/
@[stacks 0GPS] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh.isCoherent_ind :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.IsNoetherian G.U.left] [AlgebraicSpace.IsNoetherian G.R.left]
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
    [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left]
    [AlgebraicSpace.QuasiSeparated G.s.left] [AlgebraicSpace.QuasiSeparated G.t.left]
    (F : G.QCoh),
    ObjectProperty.ind.{u} (fun E : G.QCoh ↦ IsCoherent E.obj.obj) F)
