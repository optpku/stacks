/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback.StructureSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.ProjectionFormula
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BaseChange.RightAdjoint

/-! # Tensor-duality compatibility with derived base change -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/-- The canonical tensor-duality base-change comparison distributes pullback over tensor,
compares iterated pullbacks, and applies twisted base change and structure-sheaf pullback
to the right-adjoint factor. -/
def pullbackTensorDualityBaseChangeMap
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y) :
    (pullback g').obj (tensorObj ((pullback f).obj K) (a.obj (structureSheaf Y))) ⟶
      tensorObj ((pullback f').obj ((pullback g).obj K)) (a'.obj (structureSheaf Y')) :=
  pullbackTensorComparison g' ((pullback f).obj K) (a.obj (structureSheaf Y)) ≫
    tensorMap
      (pullbackSquareAppIso g' f' f g sq.toCommSq K).hom
      ((BaseChange.twistedMap g' f' f g sq a a' fAdj f'Adj hTor).app (structureSheaf Y) ≫
        a'.map (pullbackStructureSheafMap g))

/-- The tensor-duality base-change map is the pullback-tensor comparison followed by the
square and right-adjoint comparisons on the two factors. -/
theorem pullbackTensorDualityBaseChangeMap_spec
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y) :
    pullbackTensorDualityBaseChangeMap g' f' f g sq a a' fAdj f'Adj hTor K =
      pullbackTensorComparison g' ((pullback f).obj K) (a.obj (structureSheaf Y)) ≫
        tensorMap
          (pullbackSquareAppIso g' f' f g sq.toCommSq K).hom
          ((BaseChange.twistedMap g' f' f g sq a a' fAdj f'Adj hTor).app (structureSheaf Y) ≫
            a'.map (pullbackStructureSheafMap g)) :=
  sorry


/-- For a Tor-independent cartesian square, the tensor-duality maps for right adjoints
of derived pushforward commute with the canonical derived base-change comparisons. -/
theorem pullbackTensorDualityMap_baseChange
    {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y) :
    CommSq
      ((pullback g').map (pullbackTensorDualityMap f a fAdj K))
      (pullbackTensorDualityBaseChangeMap g' f' f g sq a a' fAdj f'Adj hTor K)
      ((BaseChange.twistedMap g' f' f g sq a a' fAdj f'Adj hTor).app K)
      (pullbackTensorDualityMap f' a' f'Adj ((pullback g).obj K)) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
