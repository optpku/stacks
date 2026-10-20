/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Over

/-- An object of `locallyNoetherian S` is a locally Noetherian scheme over `S`. -/
instance instIsLocallyNoetherian_locallyNoetherianObj {S : Scheme.{u}}
    (V : (locallyNoetherian S).FullSubcategory) :
    AlgebraicGeometry.IsLocallyNoetherian V.obj.left :=
  V.property

/-- Include a locally Noetherian scheme over `S` as an object of
`locallyNoetherian S`. -/
def asLocallyNoetherian {S : Scheme.{u}} (X : Over S)
    [IsLocallyNoetherian X.left] :
    (locallyNoetherian S).FullSubcategory :=
  ⟨X, ‹IsLocallyNoetherian X.left›⟩

/-- The underlying object of `asLocallyNoetherian X` is `X`. -/
theorem asLocallyNoetherian_obj {S : Scheme.{u}} (X : Over S)
    [IsLocallyNoetherian X.left] :
    (asLocallyNoetherian X).obj = X := sorry

/-- Include a morphism of locally Noetherian schemes over `S` as a morphism of
`locallyNoetherian S`. -/
def asLocallyNoetherianMap {S : Scheme.{u}} {X Y : Over S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left] (f : X ⟶ Y) :
    asLocallyNoetherian X ⟶ asLocallyNoetherian Y where
  hom := f

/-- The underlying morphism of `asLocallyNoetherianMap f` is `f`. -/
theorem asLocallyNoetherianMap_hom {S : Scheme.{u}} {X Y : Over S}
    [IsLocallyNoetherian X.left] [IsLocallyNoetherian Y.left] (f : X ⟶ Y) :
    (asLocallyNoetherianMap f).hom = f := sorry

end AlgebraicGeometry.Scheme.Over

