module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Square
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint

/-!
# Étale refinements of one-step dévissages at ambient points

This module packages the pointed comparison diagram obtained by refining a one-step
dévissage along a square of elementary étale neighbourhoods.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint

variable {S : Scheme.{u}} {X : Over S} {F : X.left.Modules}
  [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] {x : X.left}

set_option maxHeartbeats 800000 in
/-- The explicit pointed diagram refining an ambient-point one-step dévissage along a
square of elementary étale neighbourhoods. -/
structure EtaleRefinement (D : OneStepDevissageAtAmbientPoint X F x)
    (square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare
      D.toOneStepDevissage.Y.hom D.y) where
  /-- A further elementary étale neighbourhood of the refined base point. -/
  S'' : Scheme.EtaleNeighborhood.Elementary
    square.base.obj.toEtale.left square.base.obj.point
  /-- The elementary étale neighbourhood of the original source. -/
  X'' : Scheme.EtaleNeighborhood.Elementary X.left x
  /-- The structural morphism from the refined source to the further base. -/
  p'' : X''.obj.toEtale.left ⟶ S''.obj.toEtale.left
  /-- The refined structural morphism preserves the distinguished points. -/
  mapPoint : p'' X''.obj.point = S''.obj.point
  /-- The structural map to `S` is the prescribed composite through the two refined
  bases. -/
  sourceSquare : CommSq X''.obj.toEtale.hom p'' X.hom
    (S''.obj.toEtale.hom ≫ square.base.obj.toEtale.hom)
  /-- The refined source morphism is locally of finite type. -/
  refinedLocallyOfFiniteType : LocallyOfFiniteType (Over.mk p'').hom
  /-- The pullback of `F` to `X''` is quasicoherent. -/
  refinedQuasicoherent :
    ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F).IsQuasicoherent
  /-- The pullback of `F` to `X''` is of finite type. -/
  refinedFiniteType :
    ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F).IsFiniteType
  /-- The one-step dévissage of the pulled-back module at the refined ambient point. -/
  refined :
    @OneStepDevissageAtAmbientPoint S''.obj.toEtale.left (Over.mk p'')
      ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
      refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType X''.obj.point
  /-- The open embedding of the refined smooth model into the base change of the input
  smooth model. -/
  modelOpen :
    (@OneStepDevissage.Y S''.obj.toEtale.left (Over.mk p'')
      ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
      refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
      ((Over.mk p'').hom X''.obj.point)
      (@OneStepDevissageAtAmbientPoint.toOneStepDevissage S''.obj.toEtale.left
        (Over.mk p'') ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        X''.obj.point refined)).left ⟶
      Limits.pullback square.map S''.obj.toEtale.hom
  /-- The comparison map exhibits the refined smooth model as an open subscheme. -/
  modelOpenImmersion : IsOpenImmersion modelOpen
  /-- The open model comparison respects its structural map to `S''`. -/
  modelOverBase : modelOpen ≫ pullback.snd square.map S''.obj.toEtale.hom =
    (@OneStepDevissage.Y S''.obj.toEtale.left (Over.mk p'')
      ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
      refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
      ((Over.mk p'').hom X''.obj.point)
      (@OneStepDevissageAtAmbientPoint.toOneStepDevissage S''.obj.toEtale.left
        (Over.mk p'') ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        X''.obj.point refined)).hom
  /-- The distinguished model point maps to the point in the source neighbourhood. -/
  modelPointToSource :
    (modelOpen ≫ pullback.fst square.map S''.obj.toEtale.hom)
      (@OneStepDevissageAtAmbientPoint.y S''.obj.toEtale.left (Over.mk p'')
        ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        X''.obj.point refined) = square.source.obj.point
  /-- The distinguished model point maps to the point in the further base
  neighbourhood. -/
  modelPointToBase :
    (modelOpen ≫ pullback.snd square.map S''.obj.toEtale.hom)
      (@OneStepDevissageAtAmbientPoint.y S''.obj.toEtale.left (Over.mk p'')
        ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        X''.obj.point refined) = S''.obj.point
  /-- The comparison from the refined auxiliary scheme to the original one. -/
  auxiliaryToOriginal :
    (@OneStepDevissage.Z S''.obj.toEtale.left (Over.mk p'')
      ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
      refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
      ((Over.mk p'').hom X''.obj.point)
      (@OneStepDevissageAtAmbientPoint.toOneStepDevissage S''.obj.toEtale.left
        (Over.mk p'') ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        X''.obj.point refined)).left ⟶ D.toOneStepDevissage.Z.left
  /-- The refined auxiliary scheme is the pullback of the original auxiliary scheme
  along the refined smooth model. -/
  auxiliaryPullback :
    IsPullback auxiliaryToOriginal
      (@OneStepDevissage.π S''.obj.toEtale.left (Over.mk p'')
        ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        ((Over.mk p'').hom X''.obj.point)
        (@OneStepDevissageAtAmbientPoint.toOneStepDevissage S''.obj.toEtale.left
          (Over.mk p'') ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
          refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
          X''.obj.point refined)).left D.toOneStepDevissage.π.left
      (modelOpen ≫ pullback.fst square.map S''.obj.toEtale.hom ≫
        square.source.obj.toEtale.hom)
  /-- The refined closed immersion is compatible with the original one. -/
  immersionSquare :
    CommSq
      (@OneStepDevissage.i S''.obj.toEtale.left (Over.mk p'')
        ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        ((Over.mk p'').hom X''.obj.point)
        (@OneStepDevissageAtAmbientPoint.toOneStepDevissage S''.obj.toEtale.left
          (Over.mk p'') ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
          refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
          X''.obj.point refined)).left auxiliaryToOriginal X''.obj.toEtale.hom
      D.toOneStepDevissage.i.left
  /-- The auxiliary comparison preserves the distinguished point. -/
  auxiliaryPoint : auxiliaryToOriginal
    (@OneStepDevissageAtAmbientPoint.z S''.obj.toEtale.left (Over.mk p'')
      ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
      refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
      X''.obj.point refined) = D.z
  /-- The refined auxiliary module is identified with the pullback of the original
  auxiliary module. -/
  modulePullbackIso :
    (@OneStepDevissage.G S''.obj.toEtale.left (Over.mk p'')
      ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
      refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
      ((Over.mk p'').hom X''.obj.point)
      (@OneStepDevissageAtAmbientPoint.toOneStepDevissage S''.obj.toEtale.left
        (Over.mk p'') ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        X''.obj.point refined)) ≅
      (Scheme.Modules.pullback auxiliaryToOriginal).obj D.toOneStepDevissage.G

namespace EtaleRefinement

/-- Construct an étale refinement from its neighbourhoods, comparison maps, refined
dévissage, and compatibility laws. -/
def ofComponents (D : OneStepDevissageAtAmbientPoint X F x)
    (square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare
      D.toOneStepDevissage.Y.hom D.y)
    (S'' : Scheme.EtaleNeighborhood.Elementary
      square.base.obj.toEtale.left square.base.obj.point)
    (X'' : Scheme.EtaleNeighborhood.Elementary X.left x)
    (p'' : X''.obj.toEtale.left ⟶ S''.obj.toEtale.left)
    (mapPoint : p'' X''.obj.point = S''.obj.point)
    (sourceSquare : CommSq X''.obj.toEtale.hom p'' X.hom
      (S''.obj.toEtale.hom ≫ square.base.obj.toEtale.hom))
    (refinedLocallyOfFiniteType : LocallyOfFiniteType (Over.mk p'').hom)
    (refinedQuasicoherent :
      ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F).IsQuasicoherent)
    (refinedFiniteType :
      ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F).IsFiniteType)
    (refined :
      @OneStepDevissageAtAmbientPoint S''.obj.toEtale.left (Over.mk p'')
        ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType X''.obj.point)
    (modelOpen :
      (@OneStepDevissage.Y S''.obj.toEtale.left (Over.mk p'')
        ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        ((Over.mk p'').hom X''.obj.point)
        (@OneStepDevissageAtAmbientPoint.toOneStepDevissage S''.obj.toEtale.left
          (Over.mk p'') ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
          refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
          X''.obj.point refined)).left ⟶
        Limits.pullback square.map S''.obj.toEtale.hom)
    (modelOpenImmersion : IsOpenImmersion modelOpen)
    (modelOverBase : modelOpen ≫ pullback.snd square.map S''.obj.toEtale.hom =
      (@OneStepDevissage.Y S''.obj.toEtale.left (Over.mk p'')
        ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        ((Over.mk p'').hom X''.obj.point)
        (@OneStepDevissageAtAmbientPoint.toOneStepDevissage S''.obj.toEtale.left
          (Over.mk p'') ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
          refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
          X''.obj.point refined)).hom)
    (modelPointToSource :
      (modelOpen ≫ pullback.fst square.map S''.obj.toEtale.hom)
        (@OneStepDevissageAtAmbientPoint.y S''.obj.toEtale.left (Over.mk p'')
          ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
          refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
          X''.obj.point refined) = square.source.obj.point)
    (modelPointToBase :
      (modelOpen ≫ pullback.snd square.map S''.obj.toEtale.hom)
        (@OneStepDevissageAtAmbientPoint.y S''.obj.toEtale.left (Over.mk p'')
          ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
          refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
          X''.obj.point refined) = S''.obj.point)
    (auxiliaryToOriginal :
      (@OneStepDevissage.Z S''.obj.toEtale.left (Over.mk p'')
        ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        ((Over.mk p'').hom X''.obj.point)
        (@OneStepDevissageAtAmbientPoint.toOneStepDevissage S''.obj.toEtale.left
          (Over.mk p'') ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
          refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
          X''.obj.point refined)).left ⟶ D.toOneStepDevissage.Z.left)
    (auxiliaryPullback :
      IsPullback auxiliaryToOriginal
        (@OneStepDevissage.π S''.obj.toEtale.left (Over.mk p'')
          ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
          refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
          ((Over.mk p'').hom X''.obj.point)
          (@OneStepDevissageAtAmbientPoint.toOneStepDevissage S''.obj.toEtale.left
            (Over.mk p'') ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
            refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
            X''.obj.point refined)).left D.toOneStepDevissage.π.left
        (modelOpen ≫ pullback.fst square.map S''.obj.toEtale.hom ≫
          square.source.obj.toEtale.hom))
    (immersionSquare :
      CommSq
        (@OneStepDevissage.i S''.obj.toEtale.left (Over.mk p'')
          ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
          refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
          ((Over.mk p'').hom X''.obj.point)
          (@OneStepDevissageAtAmbientPoint.toOneStepDevissage S''.obj.toEtale.left
            (Over.mk p'') ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
            refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
            X''.obj.point refined)).left auxiliaryToOriginal X''.obj.toEtale.hom
        D.toOneStepDevissage.i.left)
    (auxiliaryPoint : auxiliaryToOriginal
      (@OneStepDevissageAtAmbientPoint.z S''.obj.toEtale.left (Over.mk p'')
        ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        X''.obj.point refined) = D.z)
    (modulePullbackIso :
      (@OneStepDevissage.G S''.obj.toEtale.left (Over.mk p'')
        ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
        refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
        ((Over.mk p'').hom X''.obj.point)
        (@OneStepDevissageAtAmbientPoint.toOneStepDevissage S''.obj.toEtale.left
          (Over.mk p'') ((Scheme.Modules.pullback X''.obj.toEtale.hom).obj F)
          refinedLocallyOfFiniteType refinedQuasicoherent refinedFiniteType
          X''.obj.point refined)) ≅
        (Scheme.Modules.pullback auxiliaryToOriginal).obj D.toOneStepDevissage.G) :
    EtaleRefinement D square where
  S'' := S''
  X'' := X''
  p'' := p''
  mapPoint := mapPoint
  sourceSquare := sourceSquare
  refinedLocallyOfFiniteType := refinedLocallyOfFiniteType
  refinedQuasicoherent := refinedQuasicoherent
  refinedFiniteType := refinedFiniteType
  refined := refined
  modelOpen := modelOpen
  modelOpenImmersion := modelOpenImmersion
  modelOverBase := modelOverBase
  modelPointToSource := modelPointToSource
  modelPointToBase := modelPointToBase
  auxiliaryToOriginal := auxiliaryToOriginal
  auxiliaryPullback := auxiliaryPullback
  immersionSquare := immersionSquare
  auxiliaryPoint := auxiliaryPoint
  modulePullbackIso := modulePullbackIso

/-- The refined source map preserves its point and forms the prescribed commutative
square over `S`. -/
theorem source_spec {D : OneStepDevissageAtAmbientPoint X F x}
    {square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare
      D.toOneStepDevissage.Y.hom D.y}
    (R : EtaleRefinement D square) :
    R.p'' R.X''.obj.point = R.S''.obj.point ∧
      CommSq R.X''.obj.toEtale.hom R.p'' X.hom
        (R.S''.obj.toEtale.hom ≫ square.base.obj.toEtale.hom) := sorry

/-- The open-model comparison sends its distinguished point to the prescribed points
of the source and base neighbourhoods. -/
theorem modelPoint_spec {D : OneStepDevissageAtAmbientPoint X F x}
    {square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare
      D.toOneStepDevissage.Y.hom D.y}
    (R : EtaleRefinement D square) :
    (R.modelOpen ≫ pullback.fst square.map R.S''.obj.toEtale.hom)
        (@OneStepDevissageAtAmbientPoint.y R.S''.obj.toEtale.left (Over.mk R.p'')
          ((Scheme.Modules.pullback R.X''.obj.toEtale.hom).obj F)
          R.refinedLocallyOfFiniteType R.refinedQuasicoherent R.refinedFiniteType
          R.X''.obj.point R.refined) = square.source.obj.point ∧
      (R.modelOpen ≫ pullback.snd square.map R.S''.obj.toEtale.hom)
        (@OneStepDevissageAtAmbientPoint.y R.S''.obj.toEtale.left (Over.mk R.p'')
          ((Scheme.Modules.pullback R.X''.obj.toEtale.hom).obj F)
          R.refinedLocallyOfFiniteType R.refinedQuasicoherent R.refinedFiniteType
          R.X''.obj.point R.refined) = R.S''.obj.point := sorry

end EtaleRefinement

/-- Every pointed elementary étale refinement square admits a further refinement of
an ambient-point one-step dévissage. -/
theorem nonemptyEtaleRefinement (D : OneStepDevissageAtAmbientPoint X F x)
    (square : Scheme.EtaleNeighborhood.Elementary.RefinementSquare
      D.toOneStepDevissage.Y.hom D.y) :
    Nonempty (EtaleRefinement D square) := sorry

end AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint
