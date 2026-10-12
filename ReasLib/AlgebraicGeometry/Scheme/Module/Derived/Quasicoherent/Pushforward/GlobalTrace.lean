/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.SheafyTrace
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal
open RingedSpace.Module.Derived
open RingedSpace.Module.Derived.GlobalSections

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [compactSpaceX : CompactSpace X] [quasiSeparatedSpaceX : QuasiSeparatedSpace X]
variable [quasiSeparatedSpaceY : QuasiSeparatedSpace Y]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
variable [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom f.toShHom)]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]

/-- The morphism on abelian-valued derived global sections induced by the change-of-space
comparison and the sheafy trace of a chosen derived quasicoherent pushforward adjunction. -/
noncomputable def globalTraceMap
    [compactSpaceY : CompactSpace Y]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    (RingedSpace.Module.Derived.GlobalSections.toAbelian X.toRingedSpace).obj
        ((ihom L.obj).obj (a.obj K).obj) ⟶
      (RingedSpace.Module.Derived.GlobalSections.toAbelian Y.toRingedSpace).obj
        ((ihom ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj)).obj K.obj) :=
  let restrict := RingedSpace.moduleSectionsRestrictionFunctor f.toShHom ⊤
  let forgetY := forget₂
    (ModuleCat (RingedSpace.globalSectionsRing Y.toRingedSpace)) AddCommGrpCat.{u}
  let forgetX := forget₂
    (ModuleCat (RingedSpace.globalSectionsRing X.toRingedSpace)) AddCommGrpCat.{u}
  -- Local instance justification (search instability): the universe-polymorphic module forgetful-limit instance is canonical but deliberately not inferred automatically.
  letI : Limits.PreservesLimits forgetY :=
    ModuleCat.forget₂AddCommGroup_preservesLimits
  -- Local instance justification (search instability): the universe-polymorphic module forgetful-limit instance is canonical but deliberately not inferred automatically.
  letI : Limits.PreservesFiniteLimits forgetY :=
    Limits.PreservesLimits.preservesFiniteLimits forgetY
  -- Local instance justification (search instability): the universe-polymorphic module forgetful-limit instance is canonical but deliberately not inferred automatically.
  letI : Limits.PreservesLimits forgetX :=
    ModuleCat.forget₂AddCommGroup_preservesLimits
  -- Local instance justification (search instability): the universe-polymorphic module forgetful-limit instance is canonical but deliberately not inferred automatically.
  letI : Limits.PreservesFiniteLimits forgetX :=
    Limits.PreservesLimits.preservesFiniteLimits forgetX
  let F := ExactFunctor.of restrict
  let G := ExactFunctor.of forgetY
  let H := ExactFunctor.of forgetX
  let e : restrict ⋙ forgetY ≅ forgetX :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  let e' : F.comp G ≅ H := ObjectProperty.isoMk (exactFunctor _ _) e
  ((ExactFunctor.MapDerivedCategory.compFunctorIso F G).symm ≪≫
      ExactFunctor.MapDerivedCategory.mapIso e').inv.app
      ((RingedSpace.Module.Derived.GlobalSections.functor X.toRingedSpace).obj
        ((ihom L.obj).obj (a.obj K).obj)) ≫
    forgetY.mapDerivedCategory.map
    ((RingedSpace.Module.Derived.GlobalSections.pushforwardIso f.toShHom).hom.app
      ((ihom L.obj).obj (a.obj K).obj)) ≫
    (RingedSpace.Module.Derived.GlobalSections.toAbelian Y.toRingedSpace).map
      (@InternalHom.comparison _ _ _ _ _ _
        (RingedSpace.moduleDerivedPushforward f.toShHom)
        (@CategoryTheory.Adjunction.rightAdjointLaxMonoidal _ _ _ _ _ _ _ _
          (RingedSpace.modulePullbackDerivedPushforwardAdjunction f.toShHom)
          (Functor.Monoidal.toOplaxMonoidal
            (F := RingedSpace.modulePullbackDerived f.toShHom))) L.obj (a.obj K).obj _ _ ≫
        (ihom ((RingedSpace.moduleDerivedPushforward f.toShHom).obj L.obj)).map
          ((pushforwardCohomologyIn.inclusionIso f).inv.app (a.obj K) ≫
            (inclusion Y).map (adj.counit.app K)))

/-- The global sheafy trace associated to a derived quasicoherent pushforward adjunction is an
isomorphism. -/
noncomputable instance globalTraceMapIsIso
    [compactSpaceY : CompactSpace Y]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a)
    (L : DerivedQCoh X) (K : DerivedQCoh Y) :
    IsIso (globalTraceMap f a adj L K) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
