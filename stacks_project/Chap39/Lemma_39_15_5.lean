module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.FiniteType
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 39.15.5: if the object and arrow schemes of a groupoid scheme are affine and
global sections on the arrow scheme are free over global sections on the object scheme via
the source map, then every equivariant quasi-coherent module is a small filtered colimit of
equivariant quasi-coherent modules whose underlying module sheaves are of finite type. -/
@[stacks 07TV] #check
  (AlgebraicGeometry.GroupoidScheme.QCoh.isFiniteType_ind_of_sourceFree :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      [AlgebraicGeometry.IsAffine G.U.left] [AlgebraicGeometry.IsAffine G.R.left]
      (h_free : (AlgebraicGeometry.Scheme.Hom.appTop G.s.left).hom.Free)
      (F : G.QCoh),
      CategoryTheory.ObjectProperty.ind.{u}
        (fun E : G.QCoh ↦ SheafOfModules.IsFiniteType E.obj.obj) F)
