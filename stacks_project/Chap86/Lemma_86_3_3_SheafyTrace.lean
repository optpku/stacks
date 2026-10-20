module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.SheafyTrace.Coherator

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
variable [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
variable [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
variable [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
variable [ModuleDerived.HasDerivedAdjunction f]
variable [Functor.Monoidal (ModuleDerived.pullback f)]
variable (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
variable (L : DerivedQCoh X) (K : DerivedQCoh Y)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.coheratedSheafyTraceMap f a adj L K :
  (inclusion Y).rightAdjoint.obj
      ((moduleDerivedPushforward f).obj ((ihom L.obj).obj (a.obj K).obj)) ⟶
    (inclusion Y).rightAdjoint.obj
      ((ihom ((moduleDerivedPushforward f).obj L.obj)).obj K.obj))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.coheratedSheafyTraceMap_eq_map f a adj L K :
  coheratedSheafyTraceMap f a adj L K =
    (inclusion Y).rightAdjoint.map (sheafyTraceMap f a adj L K))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.coheratedSheafyTraceMap_eq f a adj L K :
  coheratedSheafyTraceMap f a adj L K =
    (inclusion Y).rightAdjoint.map
      (@InternalHom.comparison _ _ _ _ _ _ (moduleDerivedPushforward f)
          (moduleDerivedPushforward.laxMonoidal f) L.obj (a.obj K).obj _ _ ≫
        (ihom ((moduleDerivedPushforward f).obj L.obj)).map
          ((pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj K) ≫
            (inclusion Y).map (adj.counit.app K))))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.coheratedSheafyTraceMapIsIso f a adj L K :
  IsIso (coheratedSheafyTraceMap f a adj L K))
