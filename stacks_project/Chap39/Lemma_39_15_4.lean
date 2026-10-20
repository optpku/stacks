module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Coherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open SheafOfModules

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

open Scheme.Hom

/- Lemma 39.15.4: if the object and arrow schemes of a groupoid scheme are Noetherian
and its source and target maps are flat, quasi-compact, and quasi-separated, then every
equivariant quasi-coherent module is a small filtered colimit of equivariant modules whose
underlying module sheaves are coherent. -/
@[stacks 07TU] #check
  (AlgebraicGeometry.GroupoidScheme.QCoh.isCoherent_ind :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S)
      [IsNoetherian G.U.left] [IsNoetherian G.R.left]
      [Flat G.s.left] [Flat G.t.left] [QuasiCompact G.s.left] [QuasiCompact G.t.left]
      [QuasiSeparated G.s.left] [QuasiSeparated G.t.left] (F : G.QCoh),
      ObjectProperty.ind.{u} (fun E : G.QCoh ↦ IsCoherent E.obj.obj) F)

end AlgebraicGeometry.GroupoidScheme.QCoh
