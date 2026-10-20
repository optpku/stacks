module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback

/-! # Composition and scheme restriction for quasi-coherent pullback -/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

variable {S : Scheme.{u}}

/-- Successive pullbacks of quasi-coherent modules identify canonically with pullback
along the composite morphism. -/
def pullbackCompIso {X Y Z : AlgebraicSpace S} (g : Y ⟶ Z) (f : X ⟶ Y) :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  NatIso.ofComponents
    (fun F ↦ (quasiCoherentModuleProperty X).isoMk
      ((Modules.pullbackCompIso f g).app F.obj))
    sorry

/-- The underlying forward component of the quasi-coherent composition comparison is the
canonical module pullback comparison. -/
theorem pullbackCompIso_hom_app {X Y Z : AlgebraicSpace S} (g : Y ⟶ Z)
    (f : X ⟶ Y) (F : QCoh Z) :
    ((pullbackCompIso g f).hom.app F).hom =
      (Modules.pullbackCompIso f g).hom.app F.obj :=
  rfl

/-- Restriction to the underlying schemes commutes canonically with pullback of
quasi-coherent modules along a morphism over the base. -/
def restrictPullbackIso {U V : Over S} (h : V ⟶ U) :
    pullback (ofOverMap h) ⋙ restrictToScheme V ≅
      restrictToScheme U ⋙ Scheme.QCoh.pullback h.left :=
  NatIso.ofComponents
    (fun F ↦ (Scheme.quasiCoherentModuleProperty V.left).isoMk
      ((Modules.RestrictToScheme.restrictPullbackNatIso h).app F))
    sorry

/-- The underlying forward component of the quasi-coherent restriction comparison is the
canonical module restriction and pullback comparison. -/
theorem restrictPullbackIso_hom_app {U V : Over S} (h : V ⟶ U)
    (F : QCoh (ofOver U)) :
    ((restrictPullbackIso h).hom.app F).hom =
      ((Modules.RestrictToScheme.restrictPullbackNatIso h).hom.app F) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.QCoh
