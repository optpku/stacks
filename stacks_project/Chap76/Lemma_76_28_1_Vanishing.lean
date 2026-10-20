module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Vanishing

/-! # Vanishing subspaces of finite families of global functions -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.atlasUnitSection :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (f : globalSectionsRing X),
    (SheafOfModules.unit (structureSheaf X)).val.obj (op (SmallEtale.AtlasCharts.atlasObject X)))

#check (AlgebraicGeometry.AlgebraicSpace.vanishingIdeal :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {r : ℕ}
    (fs : Fin r → globalSectionsRing X),
    IdealSubobject X)

#check (AlgebraicGeometry.AlgebraicSpace.vanishingIdeal_spec :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {r : ℕ}
    (fs : Fin r → globalSectionsRing X),
    SheafOfModules.Subobject.containsSections (vanishingIdeal fs)
      (fun _ : Fin r ↦ SmallEtale.AtlasCharts.atlasObject X) (fun i ↦ atlasUnitSection X (fs i)))

#check (AlgebraicGeometry.AlgebraicSpace.vanishingIdeal_le_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {r : ℕ}
    (fs : Fin r → globalSectionsRing X) (G : IdealSubobject X),
    vanishingIdeal fs ≤ G ↔
      SheafOfModules.Subobject.containsSections G
        (fun _ : Fin r ↦ SmallEtale.AtlasCharts.atlasObject X) (fun i ↦ atlasUnitSection X (fs i)))

#check (AlgebraicGeometry.AlgebraicSpace.vanishingIdeal.instIsQuasiCoherent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {r : ℕ} (fs : Fin r → globalSectionsRing X),
    IsQuasiCoherent (vanishingIdeal fs))

#check (AlgebraicGeometry.AlgebraicSpace.vanishingSubspace :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {r : ℕ}
    (fs : Fin r → globalSectionsRing X),
    ClosedSubspace X)

#check (AlgebraicGeometry.AlgebraicSpace.vanishingSubspace_ι :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {r : ℕ}
    (fs : Fin r → globalSectionsRing X),
    (vanishingSubspace fs).ι = subschemeι (vanishingIdeal fs))

#check (AlgebraicGeometry.AlgebraicSpace.vanishingPullback :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {r : ℕ}
    (fs : Fin r → globalSectionsRing X) (U : OpenSubspace X),
    AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.vanishingPullbackι :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {r : ℕ}
    (fs : Fin r → globalSectionsRing X) (U : OpenSubspace X),
    vanishingPullback fs U ⟶ U.X)

#check (AlgebraicGeometry.AlgebraicSpace.vanishingPullbackHom :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {r : ℕ}
    (fs : Fin r → globalSectionsRing X) (U : OpenSubspace X),
    vanishingPullback fs U ⟶ Y)
