module

public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory SheafOfModules

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh

/-- If the object and arrow spaces of a groupoid in algebraic spaces are Noetherian and
its source and target maps are flat, quasi-compact, and quasi-separated, then every
equivariant quasi-coherent module is a small filtered colimit of equivariant modules
whose underlying module sheaves are coherent. -/
theorem isCoherent_ind {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.IsNoetherian G.U.left] [AlgebraicSpace.IsNoetherian G.R.left]
    [AlgebraicSpace.Flat G.s.left] [AlgebraicSpace.Flat G.t.left]
    [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left]
    [AlgebraicSpace.QuasiSeparated G.s.left] [AlgebraicSpace.QuasiSeparated G.t.left]
    (F : G.QCoh) :
    ObjectProperty.ind.{u} (fun E : G.QCoh ↦ IsCoherent E.obj.obj) F := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
