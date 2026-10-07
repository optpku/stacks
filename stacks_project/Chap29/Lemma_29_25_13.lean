module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Descent

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.25.13: flat pullback detects relative flatness at a point. -/
@[stacks 02JZ] #check
  (AlgebraicGeometry.Scheme.Modules.flatOverAt_iff_pullback_flatOverAt_of_flatAt :
    ∀ {S X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ S)
      (𝒢 : Y.Modules) [𝒢.IsQuasicoherent] (x : X),
      Scheme.Hom.flatAt h x →
        (Scheme.Modules.flatOverAt 𝒢 f (h.base x) ↔
          Scheme.Modules.flatOverAt
            ((Scheme.Modules.pullback h).obj 𝒢) (h ≫ f) x))

#check
  (AlgebraicGeometry.Scheme.Modules.flatOver_iff_pullback_flatOver_of_surjective_of_flat :
    ∀ {S X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ S)
      (𝒢 : Y.Modules) [𝒢.IsQuasicoherent] [Flat h] [Surjective h],
      Scheme.Modules.flatOver 𝒢 f ↔
        Scheme.Modules.flatOver ((Scheme.Modules.pullback h).obj 𝒢) (h ≫ f))

#check
  (AlgebraicGeometry.Scheme.Hom.flat_of_comp_of_surjective_of_flat :
    ∀ {S X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ S)
      [Flat h] [Surjective h] [Flat (h ≫ f)], Flat f)
