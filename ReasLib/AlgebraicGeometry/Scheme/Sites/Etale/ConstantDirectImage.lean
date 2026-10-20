module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v v₁

namespace CategoryTheory.Sheaf

/-- Small-étale pushforward of a constant sheaf along a scheme morphism. -/
noncomputable abbrev pushforwardConstantSheaf {X Y : Scheme.{u}} (f : Y ⟶ X) {D : Type v}
    [Category.{v₁} D] [HasWeakSheafify X.smallEtaleTopology D]
    [HasWeakSheafify Y.smallEtaleTopology D] (E : D) :
    Sheaf X.smallEtaleTopology D :=
  ((Scheme.smallEtalePullback f).sheafPushforwardContinuous D X.smallEtaleTopology
      Y.smallEtaleTopology).obj
    ((constantSheaf Y.smallEtaleTopology D).obj E)

end CategoryTheory.Sheaf
