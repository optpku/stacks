module

import ReasLib.AlgebraicGeometry.Scheme.Module.Depth.Extension
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry ENat

universe u

/- Lemma 51.15.2 -/
@[stacks 0DX4] #check
  (AlgebraicGeometry.Scheme.Modules.IsDepthTwoExtension.unit :
    ∀ {X U : Scheme.{u}} [IsNoetherian X] [IsNoetherian U]
      (j : U ⟶ X) [IsOpenImmersion j] (F : X.Modules) [F.IsCoherent]
      [((Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj F)).IsCoherent],
      AlgebraicGeometry.Scheme.Modules.IsDepthTwoExtension j F
        ((Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj F))
        ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app F))

/- Lemma 51.15.2 -/
@[stacks 0DX4] #check
  (AlgebraicGeometry.Scheme.Modules.IsDepthTwoExtension.unit_unique :
    ∀ {X U : Scheme.{u}} [IsNoetherian X] [IsNoetherian U]
      (j : U ⟶ X) [IsOpenImmersion j] (F : X.Modules) [F.IsCoherent]
      [((Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj F)).IsCoherent]
      (φ : F ⟶ (Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj F))
      (hφ : AlgebraicGeometry.Scheme.Modules.IsDepthTwoExtension j F
        ((Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj F)) φ),
      φ = (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app F)

/- Lemma 51.15.2 -/
@[stacks 0DX4] #check
  (AlgebraicGeometry.Scheme.Modules.IsDepthTwoExtension.pullbackUnit_of_flat :
    ∀ {X U Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian U] [IsNoetherian Y]
      (j : U ⟶ X) [IsOpenImmersion j] (F : X.Modules) [F.IsCoherent]
      [((Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj F)).IsCoherent]
      (f : Y ⟶ X) [Flat f],
      AlgebraicGeometry.Scheme.Modules.IsDepthTwoExtension (Limits.pullback.fst f j)
        ((Scheme.Modules.pullback f).obj F)
        ((Scheme.Modules.pullback f).obj
          ((Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj F)))
        ((Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app F)))
