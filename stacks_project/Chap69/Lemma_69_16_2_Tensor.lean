module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ToSpec

/-! # Compatibility view of associated modules and their canonical comparisons -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u

#check (AlgebraicGeometry.AlgebraicSpace.tensorOX :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    ModuleCat.{u} (globalSectionsRing X) → X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.tensorOXSectionsUnit :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (M : ModuleCat.{u} (globalSectionsRing X)),
    M ⟶ moduleGlobalSections X (tensorOX X M))

#check (AlgebraicGeometry.AlgebraicSpace.tensorOXPushforwardUnit :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (M : ModuleCat.{u} (globalSectionsRing X)),
    (AlgebraicGeometry.tilde.functor (globalSectionsRing X)).obj M ⟶
      (toSpecAPushforward X).obj (tensorOX X M))
