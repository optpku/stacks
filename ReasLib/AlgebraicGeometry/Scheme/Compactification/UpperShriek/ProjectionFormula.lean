/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RightAdjoint.Composition

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalCategory
open DerivedCategory.TStructure
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u


namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

/-- The unbounded compactification model for upper shriek: first apply the chosen
right adjoint for the proper ambient morphism and then pull back to the open interior. -/
noncomputable def ambient
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    DerivedQCoh Y.obj.left ⥤ DerivedQCoh X.obj.left :=
  A.right ⋙ DerivedQCoh.pullback (ι P)

/-- The compactification factorization identifies iterated derived pullback with
derived pullback along the original finite-type separated morphism. -/
noncomputable def pullbackFactorIso
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left)) :
    DerivedQCoh.pullback (ambientMorphism P) ⋙ DerivedQCoh.pullback (ι P) ≅
      DerivedQCoh.pullback f.hom.left :=
  DerivedQCoh.pullbackCompIso (ι P) (ambientMorphism P)
      (RingedSpace.modulePullbackDerived.compComparison_isIso
        (ι P).toShHom (ambientMorphism P).toShHom) ≪≫
    eqToIso (congrArg DerivedQCoh.pullback P.obj.hom.w)

/-- The bounded upper-shriek model agrees, after forgetting boundedness, with its
unbounded compactification model. -/
noncomputable def restrictionIso
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) :
    upperShriek f P A.plus ⋙
        DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty X.obj.left.toRingedSpace) ≅
      DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace) ⋙
        ambient f P A :=
  ((ModuleDerived.quasicoherentProperty X.obj.left).fullyFaithfulι.whiskeringRight
      (DerivedQCoh.Plus Y.obj.left)).preimageIso
    (A.openRestrictionAmbientIso (ι P))

/-- The compactification model of `f⁺!𝒪_Y`. -/
noncomputable def dualizingObject
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P)) : DerivedQCoh X.obj.left :=
  (ambient f P A).obj (DerivedQCoh.structureSheaf Y.obj.left)

/-- The canonical source comparison for the upper-shriek projection-formula map. -/
noncomputable def tensorSourceIso
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [HomotopyTensorDescends (Of.ambient P).toRingedSpace]
    [TensorDescends (Of.ambient P).toRingedSpace]
    [IsLocalization (Of.ambient P).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism P).toShHom)]
    [interiorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι P).toShHom)]
    (K : DerivedQCoh Y.obj.left) :
    DerivedQCoh.tensorObj ((DerivedQCoh.pullback f.hom.left).obj K)
        (dualizingObject f P A) ≅
      (DerivedQCoh.pullback (ι P)).obj
        (DerivedQCoh.tensorObj
          ((DerivedQCoh.pullback (ambientMorphism P)).obj K)
          (A.right.obj (DerivedQCoh.structureSheaf Y.obj.left))) :=
  (DerivedQCoh.tensorRight (dualizingObject f P A)).mapIso
      ((pullbackFactorIso f P).symm.app K) ≪≫
    (DerivedQCoh.pullbackTensorIso (ι P)
      ((DerivedQCoh.pullback (ambientMorphism P)).obj K)
      (A.right.obj (DerivedQCoh.structureSheaf Y.obj.left))).symm

/-- The canonical map
`Lf^*K ⊗ᴸ f⁺!𝒪_Y ⟶ f⁺!K` in the unbounded compactification model. -/
noncomputable def tensorMap
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [HomotopyTensorDescends (Of.ambient P).toRingedSpace]
    [TensorDescends (Of.ambient P).toRingedSpace]
    [IsLocalization (Of.ambient P).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism P).toShHom)]
    [ambientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism P).toShHom)]
    [interiorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι P).toShHom)]
    (K : DerivedQCoh Y.obj.left) :
    DerivedQCoh.tensorObj ((DerivedQCoh.pullback f.hom.left).obj K)
        (dualizingObject f P A) ⟶ (ambient f P A).obj K :=
  (tensorSourceIso f P A K).hom ≫
    (DerivedQCoh.pullback (ι P)).map
      (DerivedQCoh.pullbackTensorDualityMap
        (ambientMorphism P) A.right A.adjunction K)

/-- The maps `tensorMap f P A K` are natural in `K`. -/
theorem tensorMap_naturality
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [HomotopyTensorDescends (Of.ambient P).toRingedSpace]
    [TensorDescends (Of.ambient P).toRingedSpace]
    [IsLocalization (Of.ambient P).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism P).toShHom)]
    [ambientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism P).toShHom)]
    [interiorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι P).toShHom)]
    {K L : DerivedQCoh Y.obj.left} (φ : K ⟶ L) :
    (DerivedQCoh.pullback f.hom.left ⋙
        DerivedQCoh.tensorRight (dualizingObject f P A)).map φ ≫
        tensorMap f P A L =
      tensorMap f P A K ≫ (ambient f P A).map φ := sorry

/-- The upper-shriek projection-formula maps, packaged as a natural transformation
on the unbounded derived quasicoherent category. -/
noncomputable def tensorNatTrans
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [HomotopyTensorDescends (Of.ambient P).toRingedSpace]
    [TensorDescends (Of.ambient P).toRingedSpace]
    [IsLocalization (Of.ambient P).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism P).toShHom)]
    [ambientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism P).toShHom)]
    [interiorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι P).toShHom)] :
    DerivedQCoh.pullback f.hom.left ⋙
        DerivedQCoh.tensorRight (dualizingObject f P A) ⟶ ambient f P A where
  app K := tensorMap f P A K
  naturality _ _ φ := tensorMap_naturality f P A φ

/-- The component of `tensorNatTrans` is the canonical map `tensorMap`. -/
theorem tensorNatTrans_app
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [HomotopyTensorDescends (Of.ambient P).toRingedSpace]
    [TensorDescends (Of.ambient P).toRingedSpace]
    [IsLocalization (Of.ambient P).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism P).toShHom)]
    [ambientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism P).toShHom)]
    [interiorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι P).toShHom)]
    (K : DerivedQCoh Y.obj.left) :
    (tensorNatTrans f P A).app K = tensorMap f P A K := sorry

/-- The canonical maps `Lf^*K ⊗ᴸ f⁺!𝒪_Y ⟶ f⁺!K`, functorial for
bounded-below `K`, with the target transported to the chosen upper-shriek model. -/
noncomputable def tensorNatTransPlus
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [HomotopyTensorDescends (Of.ambient P).toRingedSpace]
    [TensorDescends (Of.ambient P).toRingedSpace]
    [IsLocalization (Of.ambient P).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism P).toShHom)]
    [ambientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism P).toShHom)]
    [interiorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (Of.ambient P).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (Of.ambient P).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι P).toShHom)] :
    DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace) ⋙
        (DerivedQCoh.pullback f.hom.left ⋙
          DerivedQCoh.tensorRight (dualizingObject f P A)) ⟶
      upperShriek f P A.plus ⋙
        DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty X.obj.left.toRingedSpace) :=
  Functor.whiskerLeft
      (DerivedCategory.Plus.CohomologyIn.toUnbounded
        (RingedSpace.quasiCoherentModuleProperty Y.obj.left.toRingedSpace))
      (tensorNatTrans f P A) ≫
    (restrictionIso f P A).inv

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek

namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriekCompChoice

/-- After forgetting boundedness, the upper-shriek compositor identifies the
compactification model for `f ≫ g` with the iterated compactification models. -/
noncomputable def ambientCompIso
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g) :
    DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace) ⋙
        UpperShriek.ambient (f ≫ g) (comp f g C.P_g C.P_bar) C.A_fg ≅
      (DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace) ⋙
        UpperShriek.ambient g C.P_g C.A_g) ⋙
          UpperShriek.ambient f C.P_f C.A_f :=
  (UpperShriek.restrictionIso (f ≫ g) (comp f g C.P_g C.P_bar) C.A_fg).symm ≪≫
    Functor.isoWhiskerRight (C.compIso f g)
      (DerivedCategory.Plus.CohomologyIn.toUnbounded
        (RingedSpace.quasiCoherentModuleProperty X.obj.left.toRingedSpace)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (upperShriek g C.P_g C.A_g.plus)
      (UpperShriek.restrictionIso f C.P_f C.A_f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (UpperShriek.restrictionIso g C.P_g C.A_g)
      (UpperShriek.ambient f C.P_f C.A_f) ≪≫
    Functor.associator _ _ _

/-- Evaluating `ambientCompIso` at the bounded-below structure sheaf gives the
canonical identification `(f ≫ g)⁺!𝒪_Z ≅ f⁺!g⁺!𝒪_Z`. -/
noncomputable def dualizingIso
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g) :
    UpperShriek.dualizingObject (f ≫ g) (comp f g C.P_g C.P_bar) C.A_fg ≅
      (UpperShriek.ambient f C.P_f C.A_f).obj
        (UpperShriek.dualizingObject g C.P_g C.A_g) :=
  (UpperShriek.ambient (f ≫ g) (comp f g C.P_g C.P_bar) C.A_fg).mapIso
      (DerivedQCoh.structureSheafPlusIso Z.obj.left).symm ≪≫
    (ambientCompIso f g C).app (DerivedQCoh.structureSheafPlus Z.obj.left) ≪≫
    (UpperShriek.ambient f C.P_f C.A_f).mapIso
      ((UpperShriek.ambient g C.P_g C.A_g).mapIso
        (DerivedQCoh.structureSheafPlusIso Z.obj.left))

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriekCompChoice


namespace AlgebraicGeometry.Scheme.Compactification.Of.UpperShriekCompChoice

/-- The canonical source-side identification in the upper-shriek composition
diagram: distribute `Lf^*` over tensor product and compose the two pullbacks. -/
noncomputable def tensorSourceIso
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g)
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [fPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory X.obj.left.toRingedSpace)
      (RingedSpace.modulePullbackDerived f.hom.left.toShHom)]
    (K : DerivedQCoh.Plus Z.obj.left) :
    DerivedQCoh.tensorObj
        ((DerivedQCoh.pullback f.hom.left).obj
          (DerivedQCoh.tensorObj
            ((DerivedQCoh.pullback g.hom.left).obj
              ((DerivedCategory.Plus.CohomologyIn.toUnbounded
                (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace)).obj K))
            (UpperShriek.dualizingObject g C.P_g C.A_g)))
        (UpperShriek.dualizingObject f C.P_f C.A_f) ≅
      DerivedQCoh.tensorObj
        (DerivedQCoh.tensorObj
          ((DerivedQCoh.pullback (f ≫ g).hom.left).obj
            ((DerivedCategory.Plus.CohomologyIn.toUnbounded
              (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace)).obj K))
          ((DerivedQCoh.pullback f.hom.left).obj
            (UpperShriek.dualizingObject g C.P_g C.A_g)))
        (UpperShriek.dualizingObject f C.P_f C.A_f) :=
  DerivedQCoh.pullbackTensorCompIso f.hom.left g.hom.left
    (RingedSpace.modulePullbackDerived.compComparison_isIso
      f.hom.left.toShHom g.hom.left.toShHom)
    ((DerivedCategory.Plus.CohomologyIn.toUnbounded
      (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace)).obj K)
    (UpperShriek.dualizingObject g C.P_g C.A_g)
    (UpperShriek.dualizingObject f C.P_f C.A_f)

/-- The upper route in the composition diagram: first apply the duality map for `f`,
then apply the compactification model of `f⁺!` to the duality map for `g`. -/
noncomputable def tensorTop
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g)
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends (Over.mk g.hom.left).left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [IsLocalization (Over.mk g.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Z.obj.left.toRingedSpace]
    [TensorDescends Z.obj.left.toRingedSpace]
    [IsLocalization Z.obj.left.toRingedSpace]
    [HomotopyTensorDescends (ambient C.P_f).toRingedSpace]
    [TensorDescends (ambient C.P_f).toRingedSpace]
    [IsLocalization (ambient C.P_f).toRingedSpace]
    [HomotopyTensorDescends (ambient C.P_g).toRingedSpace]
    [TensorDescends (ambient C.P_g).toRingedSpace]
    [IsLocalization (ambient C.P_g).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism C.P_f).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism C.P_g).toShHom)]
    [fAmbientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (ambient C.P_f).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_f).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism C.P_f).toShHom)]
    [fInteriorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (ambient C.P_f).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_f).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι C.P_f).toShHom)]
    [gAmbientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Z.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Z.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (ambient C.P_g).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_g).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism C.P_g).toShHom)]
    [gInteriorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (ambient C.P_g).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_g).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk g.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk g.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι C.P_g).toShHom)]
    (K : DerivedQCoh.Plus Z.obj.left) :
    DerivedQCoh.tensorObj
        ((DerivedQCoh.pullback f.hom.left).obj
          (DerivedQCoh.tensorObj
            ((DerivedQCoh.pullback g.hom.left).obj
              ((DerivedCategory.Plus.CohomologyIn.toUnbounded
                (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace)).obj K))
            (UpperShriek.dualizingObject g C.P_g C.A_g)))
        (UpperShriek.dualizingObject f C.P_f C.A_f) ⟶
      (UpperShriek.ambient f C.P_f C.A_f).obj
        ((UpperShriek.ambient g C.P_g C.A_g).obj
          ((DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace)).obj K)) :=
  UpperShriek.tensorMap f C.P_f C.A_f
      (DerivedQCoh.tensorObj
        ((DerivedQCoh.pullback g.hom.left).obj
          ((DerivedCategory.Plus.CohomologyIn.toUnbounded
            (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace)).obj K))
        (UpperShriek.dualizingObject g C.P_g C.A_g)) ≫
    (UpperShriek.ambient f C.P_f C.A_f).map
      (UpperShriek.tensorMap g C.P_g C.A_g
        ((DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace)).obj K))

/-- The lower route in the composition diagram: compose pullbacks, apply the `f`
duality map to the two dualizing factors, identify the composite dualizing object,
and then apply the duality map for `f ≫ g`. -/
noncomputable def tensorBottom
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g)
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [TensorDescends (Over.mk (f ≫ g).hom.left).left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization (Over.mk (f ≫ g).hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [HomotopyTensorDescends Z.obj.left.toRingedSpace]
    [TensorDescends Z.obj.left.toRingedSpace]
    [IsLocalization Z.obj.left.toRingedSpace]
    [HomotopyTensorDescends (ambient C.P_f).toRingedSpace]
    [TensorDescends (ambient C.P_f).toRingedSpace]
    [IsLocalization (ambient C.P_f).toRingedSpace]
    [HomotopyTensorDescends (ambient (comp f g C.P_g C.P_bar)).toRingedSpace]
    [TensorDescends (ambient (comp f g C.P_g C.P_bar)).toRingedSpace]
    [IsLocalization (ambient (comp f g C.P_g C.P_bar)).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism C.P_f).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom
      (ambientMorphism (comp f g C.P_g C.P_bar)).toShHom)]
    [fAmbientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (ambient C.P_f).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_f).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism C.P_f).toShHom)]
    [fInteriorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (ambient C.P_f).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_f).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι C.P_f).toShHom)]
    [fgAmbientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Z.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Z.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (ambient (comp f g C.P_g C.P_bar)).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (ambient (comp f g C.P_g C.P_bar)).toRingedSpace)
      (RingedSpace.modulePullbackDerived
        (ambientMorphism (comp f g C.P_g C.P_bar)).toShHom)]
    [fgInteriorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (ambient (comp f g C.P_g C.P_bar)).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (ambient (comp f g C.P_g C.P_bar)).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk (f ≫ g).hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk (f ≫ g).hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι (comp f g C.P_g C.P_bar)).toShHom)]
    (K : DerivedQCoh.Plus Z.obj.left) :
    DerivedQCoh.tensorObj
        (DerivedQCoh.tensorObj
          ((DerivedQCoh.pullback (f ≫ g).hom.left).obj
            ((DerivedCategory.Plus.CohomologyIn.toUnbounded
              (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace)).obj K))
          ((DerivedQCoh.pullback f.hom.left).obj
            (UpperShriek.dualizingObject g C.P_g C.A_g)))
        (UpperShriek.dualizingObject f C.P_f C.A_f) ⟶
      (UpperShriek.ambient (f ≫ g) (comp f g C.P_g C.P_bar) C.A_fg).obj
        ((DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace)).obj K) :=
  DerivedQCoh.tensorObjAssocMapRight
      ((DerivedQCoh.pullback (f ≫ g).hom.left).obj
        ((DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace)).obj K))
      ((DerivedQCoh.pullback f.hom.left).obj
        (UpperShriek.dualizingObject g C.P_g C.A_g))
      (UpperShriek.dualizingObject f C.P_f C.A_f)
      ((UpperShriek.ambient f C.P_f C.A_f).obj
        (UpperShriek.dualizingObject g C.P_g C.A_g))
      (UpperShriek.tensorMap f C.P_f C.A_f
        (UpperShriek.dualizingObject g C.P_g C.A_g)) ≫
    DerivedQCoh.tensorObjMapRight
      ((DerivedQCoh.pullback (f ≫ g).hom.left).obj
        ((DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace)).obj K))
      (dualizingIso f g C).inv ≫
    UpperShriek.tensorMap (f ≫ g) (comp f g C.P_g C.P_bar) C.A_fg
      ((DerivedCategory.Plus.CohomologyIn.toUnbounded
        (RingedSpace.quasiCoherentModuleProperty Z.obj.left.toRingedSpace)).obj K)

/-- The upper-shriek projection-formula maps are compatible with composition,
with every vertical identification represented by its canonical isomorphism. -/
theorem tensorCommSq
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y Z : FiniteTypeSeparatedOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (C : UpperShriekCompChoice f g)
    [HomotopyTensorDescends X.obj.left.toRingedSpace]
    [TensorDescends X.obj.left.toRingedSpace]
    [TensorDescends (Over.mk f.hom.left).left.toRingedSpace]
    [TensorDescends (Over.mk (f ≫ g).hom.left).left.toRingedSpace]
    [IsLocalization X.obj.left.toRingedSpace]
    [IsLocalization (Over.mk f.hom.left).left.toRingedSpace]
    [IsLocalization (Over.mk (f ≫ g).hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends Y.obj.left.toRingedSpace]
    [TensorDescends (Over.mk g.hom.left).left.toRingedSpace]
    [IsLocalization Y.obj.left.toRingedSpace]
    [IsLocalization (Over.mk g.hom.left).left.toRingedSpace]
    [HomotopyTensorDescends Z.obj.left.toRingedSpace]
    [TensorDescends Z.obj.left.toRingedSpace]
    [IsLocalization Z.obj.left.toRingedSpace]
    [HomotopyTensorDescends (ambient C.P_f).toRingedSpace]
    [TensorDescends (ambient C.P_f).toRingedSpace]
    [IsLocalization (ambient C.P_f).toRingedSpace]
    [HomotopyTensorDescends (ambient C.P_g).toRingedSpace]
    [TensorDescends (ambient C.P_g).toRingedSpace]
    [IsLocalization (ambient C.P_g).toRingedSpace]
    [HomotopyTensorDescends (ambient (comp f g C.P_g C.P_bar)).toRingedSpace]
    [TensorDescends (ambient (comp f g C.P_g C.P_bar)).toRingedSpace]
    [IsLocalization (ambient (comp f g C.P_g C.P_bar)).toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism C.P_f).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom (ambientMorphism C.P_g).toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom
      (ambientMorphism (comp f g C.P_g C.P_bar)).toShHom)]
    [fPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived X.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory X.obj.left.toRingedSpace)
      (RingedSpace.modulePullbackDerived f.hom.left.toShHom)]
    [fAmbientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Y.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Y.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (ambient C.P_f).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_f).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism C.P_f).toShHom)]
    [fInteriorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (ambient C.P_f).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_f).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk f.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk f.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι C.P_f).toShHom)]
    [gAmbientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Z.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Z.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (ambient C.P_g).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_g).toRingedSpace)
      (RingedSpace.modulePullbackDerived (ambientMorphism C.P_g).toShHom)]
    [gInteriorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (ambient C.P_g).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory (ambient C.P_g).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk g.hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk g.hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι C.P_g).toShHom)]
    [fgAmbientPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived Z.obj.left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory Z.obj.left.toRingedSpace)
      (RingedSpace.ModuleDerived (ambient (comp f g C.P_g C.P_bar)).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (ambient (comp f g C.P_g C.P_bar)).toRingedSpace)
      (RingedSpace.modulePullbackDerived
        (ambientMorphism (comp f g C.P_g C.P_bar)).toShHom)]
    [fgInteriorPullbackMonoidal : @Functor.Monoidal
      (RingedSpace.ModuleDerived (ambient (comp f g C.P_g C.P_bar)).toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (ambient (comp f g C.P_g C.P_bar)).toRingedSpace)
      (RingedSpace.ModuleDerived (Over.mk (f ≫ g).hom.left).left.toRingedSpace) _
        (RingedSpace.ModuleDerived.monoidalCategory
          (Over.mk (f ≫ g).hom.left).left.toRingedSpace)
      (RingedSpace.modulePullbackDerived (ι (comp f g C.P_g C.P_bar)).toShHom)]
    (K : DerivedQCoh.Plus Z.obj.left) :
    CommSq (tensorTop f g C K) (tensorSourceIso f g C K).hom
      ((ambientCompIso f g C).inv.app K) (tensorBottom f g C K) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of.UpperShriekCompChoice
