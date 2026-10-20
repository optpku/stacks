/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BaseChange.RightAdjoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.TotalComposition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Permanence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Permanence
public import ReasLib.CategoryTheory.Adjunction.BaseChange.VerticalComposition
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Vertical composition of right-adjoint base change

Right-adjoint base-change maps for stacked Tor-independent cartesian squares
compose to the map for the outer rectangle through canonical composition
isomorphisms and uniqueness of right adjoints.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

/-- For two vertically stacked Tor-independent cartesian squares of quasi-compact,
quasi-separated algebraic spaces, the right-adjoint base-change maps compose to
the map for the outer rectangle. The comparisons are induced by canonical derived
pushforward composition and uniqueness of right adjoints, and the equality holds
on every derived object with quasi-coherent cohomology. -/
theorem rightAdjointBaseChange_verticalComposition {S : Scheme.{u}}
    {X' X Y' Y Z' Z : AlgebraicSpace S}
    [IsQuasiCompact X'] [IsAbsolutelyQuasiSeparated X']
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact Y'] [IsAbsolutelyQuasiSeparated Y']
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [IsQuasiCompact Z'] [IsAbsolutelyQuasiSeparated Z']
    [IsQuasiCompact Z] [IsAbsolutelyQuasiSeparated Z]
    (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y)
    (g' : Y' ⟶ Z') (g : Y ⟶ Z) (m : Z' ⟶ Z)
    (top : IsPullback k f' f l) (bottom : IsPullback l g' g m)
    (hTop : TorIndependentOver (Over.mk f) (Over.mk l))
    (hBottom : TorIndependentOver (Over.mk g) (Over.mk m))
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (b : DerivedQCoh Z ⥤ DerivedQCoh Y) (b' : DerivedQCoh Z' ⥤ DerivedQCoh Y')
    (c : DerivedQCoh Z ⥤ DerivedQCoh X) (c' : DerivedQCoh Z' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a) (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (gAdj : pushforwardCohomologyIn g ⊣ b) (g'Adj : pushforwardCohomologyIn g' ⊣ b')
    (compAdj : pushforwardCohomologyIn (f ≫ g) ⊣ c)
    (comp'Adj : pushforwardCohomologyIn (f' ≫ g') ⊣ c') (K : DerivedQCoh Z) :
    let pullComp : pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
      ((derivedQuasiCoherentModuleProperty X).fullyFaithfulι.whiskeringRight _).preimageIso
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (pullback g) (pullback.inclusionIso f) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (pullback.inclusionIso g) (Functor.LeftDerived.Homotopy.functor (Modules.pullback f)) ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (inclusion Z)
            (ModuleDerived.totalPullbackCompIso f g) ≪≫
          (pullback.inclusionIso (f ≫ g)).symm)
    let pullComp' : pullback g' ⋙ pullback f' ≅ pullback (f' ≫ g') :=
      ((derivedQuasiCoherentModuleProperty X').fullyFaithfulι.whiskeringRight _).preimageIso
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (pullback g') (pullback.inclusionIso f') ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (pullback.inclusionIso g') (Functor.LeftDerived.Homotopy.functor (Modules.pullback f')) ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (inclusion Z')
            (ModuleDerived.totalPullbackCompIso f' g') ≪≫
          (pullback.inclusionIso (f' ≫ g')).symm)
    let pushComp :=
      (((pullbackPushforwardCohomologyAdjunction g).comp
        (pullbackPushforwardCohomologyAdjunction f)).ofNatIsoLeft pullComp).rightAdjointUniq
          (pullbackPushforwardCohomologyAdjunction (f ≫ g))
    let pushComp' :=
      (((pullbackPushforwardCohomologyAdjunction g').comp
        (pullbackPushforwardCohomologyAdjunction f')).ofNatIsoLeft pullComp').rightAdjointUniq
          (pullbackPushforwardCohomologyAdjunction (f' ≫ g'))
    let cIso := ((fAdj.comp gAdj).ofNatIsoLeft pushComp).rightAdjointUniq compAdj
    let c'Iso := ((f'Adj.comp g'Adj).ofNatIsoLeft pushComp').rightAdjointUniq comp'Adj
    let gammaTop := DerivedBaseChange.mapOfRight
      (pullbackPushforwardCohomologyAdjunction l) (pullbackPushforwardCohomologyAdjunction k)
      (@inv _ _ _ _ (BaseChange.rightMate k f' f l top.toCommSq a a' fAdj f'Adj)
        (BaseChange.rightMate_isIso_of_torIndependent k f' f l top a a' fAdj f'Adj hTop))
    let gammaBottom := DerivedBaseChange.mapOfRight
      (pullbackPushforwardCohomologyAdjunction m) (pullbackPushforwardCohomologyAdjunction l)
      (@inv _ _ _ _ (BaseChange.rightMate l g' g m bottom.toCommSq b b' gAdj g'Adj)
        (BaseChange.rightMate_isIso_of_torIndependent l g' g m bottom b b' gAdj g'Adj
          hBottom))
    let rectangle := top.paste_vert bottom
    let hRectangle := torIndependentOver_verticalComposition k f' f l g' g m
      top bottom hTop hBottom
    let gammaRectangle := DerivedBaseChange.mapOfRight
      (pullbackPushforwardCohomologyAdjunction m) (pullbackPushforwardCohomologyAdjunction k)
      (@inv _ _ _ _
        (BaseChange.rightMate k (f' ≫ g') (f ≫ g) m rectangle.toCommSq c c' compAdj comp'Adj)
        (BaseChange.rightMate_isIso_of_torIndependent k (f' ≫ g') (f ≫ g) m
          rectangle c c' compAdj comp'Adj hRectangle))
    (pullback k).map (cIso.hom.app K) ≫ gammaRectangle.app K =
      gammaTop.app (b.obj K) ≫ a'.map (gammaBottom.app K) ≫
        c'Iso.hom.app ((pullback m).obj K) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange
