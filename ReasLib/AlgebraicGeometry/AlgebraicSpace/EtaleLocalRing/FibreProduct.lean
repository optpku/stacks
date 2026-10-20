module

public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.Algebra.Category.ModuleCat.Tor.TensorAction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.Functoriality

/-!
# Local rings and Tor modules at fibre-product geometric points
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open CategoryTheory.ModuleCat.Tor
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FibreProduct

variable {S : Scheme.{u}}
variable {B X Y : AlgebraicSpace S}

/-- The étale local ring `R = 𝒪_{B, b̄}` at the image of a geometric point of `X ×_B Y`. -/
abbrev stalkBase (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) : Type u :=
  etaleLocalRing B (xybar.map (pullback.fst f g ≫ f))

/-- Unfolding of `stalkBase` as the étale local ring of `B` at `xybar.map (pullback.fst f g ≫ f)`. -/
theorem stalkBase_eq (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkBase f g xybar = etaleLocalRing B (xybar.map (pullback.fst f g ≫ f)) :=
  rfl

/-- The étale local ring `A = 𝒪_{X, x̄}` at the image of a geometric point of `X ×_B Y`. -/
abbrev stalkX (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) : Type u :=
  etaleLocalRing X (xybar.map (pullback.fst f g))

/-- Unfolding of `stalkX` as the étale local ring of `X` at `xybar.map (pullback.fst f g)`. -/
theorem stalkX_eq (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkX f g xybar = etaleLocalRing X (xybar.map (pullback.fst f g)) :=
  rfl

/-- The étale local ring `𝒪_{Y, ȳ}` at the image of a geometric point of `X ×_B Y`. -/
abbrev stalkY (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) : Type u :=
  etaleLocalRing Y (xybar.map (pullback.snd f g))

/-- Unfolding of `stalkY` as the étale local ring of `Y` at `xybar.map (pullback.snd f g)`. -/
theorem stalkY_eq (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkY f g xybar = etaleLocalRing Y (xybar.map (pullback.snd f g)) :=
  rfl

/-- The étale local ring `C = 𝒪_{X ×_B Y, (x̄, ȳ)}` at a geometric point of the fibre product. -/
abbrev stalkW (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) : Type u :=
  etaleLocalRing (pullback f g) xybar

/-- Unfolding of `stalkW` as the étale local ring of `X ×_B Y` at `xybar`. -/
theorem stalkW_eq (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkW f g xybar = etaleLocalRing (pullback f g) xybar :=
  rfl

/-- The local ring map `R →+* A` obtained from `X ⟶ B` after identifying
`xybar.map (pullback.fst f g ≫ f)` with `(xybar.map (pullback.fst f g)).map f`. -/
def algebraMapStalkBaseStalkX (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    stalkBase f g xybar →+* stalkX f g xybar :=
  (etaleLocalRingMap f (xybar.map (pullback.fst f g))).comp
    (Eq.rec (motive := fun p _ ↦ stalkBase f g xybar →+* etaleLocalRing B p)
      (RingHom.id (stalkBase f g xybar)) (map_comp xybar (pullback.fst f g) f))

/-- Unfolding of `algebraMapStalkBaseStalkX` through `etaleLocalRingMap` and `map_comp`. -/
theorem algebraMapStalkBaseStalkX_eq (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    algebraMapStalkBaseStalkX f g xybar =
      (etaleLocalRingMap f (xybar.map (pullback.fst f g))).comp
        (Eq.rec (motive := fun p _ ↦ stalkBase f g xybar →+* etaleLocalRing B p)
          (RingHom.id (stalkBase f g xybar)) (map_comp xybar (pullback.fst f g) f)) :=
  rfl

/-- The local ring map `R →+* 𝒪_{Y, ȳ}` obtained from `Y ⟶ B` after identifying
`xybar.map (pullback.fst f g ≫ f)` with `(xybar.map (pullback.snd f g)).map g`. -/
def algebraMapStalkBaseStalkY (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    stalkBase f g xybar →+* stalkY f g xybar :=
  (etaleLocalRingMap g (xybar.map (pullback.snd f g))).comp
    (((congrArg (fun h ↦ xybar.map h) pullback.condition).trans
      (map_comp xybar (pullback.snd f g) g)) ▸ RingHom.id (stalkBase f g xybar))

/-- Unfolding of `algebraMapStalkBaseStalkY` through `etaleLocalRingMap`, `map_comp`, and
`pullback.condition`. -/
theorem algebraMapStalkBaseStalkY_eq (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    algebraMapStalkBaseStalkY f g xybar =
      (etaleLocalRingMap g (xybar.map (pullback.snd f g))).comp
        (((congrArg (fun h ↦ xybar.map h) pullback.condition).trans
          (map_comp xybar (pullback.snd f g) g)) ▸ RingHom.id (stalkBase f g xybar)) :=
  rfl

/-- The `R`-algebra structure on `A = 𝒪_{X, x̄}`. -/
instance instAlgebraStalkBaseStalkX (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    Algebra (stalkBase f g xybar) (stalkX f g xybar) :=
  (algebraMapStalkBaseStalkX f g xybar).toAlgebra

/-- The `R`-algebra structure on `𝒪_{Y, ȳ}`. -/
instance instAlgebraStalkBaseStalkY (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    Algebra (stalkBase f g xybar) (stalkY f g xybar) :=
  (algebraMapStalkBaseStalkY f g xybar).toAlgebra

/-- The algebra structure on the fibre-product local ring induced by its map to the base. -/
instance instAlgebraStalkBaseStalkW (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    Algebra (stalkBase f g xybar) (stalkW f g xybar) :=
  (etaleLocalRingMap (pullback.fst f g ≫ f) xybar).toAlgebra

/-- The `R`-algebra map `A →ₐ[R] C` induced by the projection `X ×_B Y ⟶ X`. -/
def algHomStalkXStalkW (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkX f g xybar →ₐ[stalkBase f g xybar] stalkW f g xybar :=
  { etaleLocalRingMap (pullback.fst f g) xybar with commutes' := sorry }

/-- Unfolding of `algHomStalkXStalkW` as `etaleLocalRingMap` of `pullback.fst`. -/
theorem algHomStalkXStalkW_toRingHom (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    (algHomStalkXStalkW f g xybar).toRingHom =
      etaleLocalRingMap (pullback.fst f g) xybar :=
  rfl

/-- The `R`-algebra map `𝒪_{Y, ȳ} →ₐ[R] C` induced by the projection `X ×_B Y ⟶ Y`. -/
def algHomStalkYStalkW (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkY f g xybar →ₐ[stalkBase f g xybar] stalkW f g xybar :=
  { etaleLocalRingMap (pullback.snd f g) xybar with commutes' := sorry }

/-- Unfolding of `algHomStalkYStalkW` as `etaleLocalRingMap` of `pullback.snd`. -/
theorem algHomStalkYStalkW_toRingHom (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    (algHomStalkYStalkW f g xybar).toRingHom =
      etaleLocalRingMap (pullback.snd f g) xybar :=
  rfl

/-- The product map `A ⊗[R] 𝒪_{Y, ȳ} →ₐ[R] C` of the two projection local-ring maps. -/
def tensorStalkProductMap (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkX f g xybar ⊗[stalkBase f g xybar] stalkY f g xybar →ₐ[stalkBase f g xybar]
      stalkW f g xybar :=
  Algebra.TensorProduct.productMap (algHomStalkXStalkW f g xybar)
    (algHomStalkYStalkW f g xybar)

/-- Unfolding of `tensorStalkProductMap` as `Algebra.TensorProduct.productMap`. -/
theorem tensorStalkProductMap_eq (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    tensorStalkProductMap f g xybar =
      Algebra.TensorProduct.productMap (algHomStalkXStalkW f g xybar)
        (algHomStalkYStalkW f g xybar) :=
  rfl

/-- `Tor_1^R(A, 𝒪_{Y, ȳ})` base-changed to `C = 𝒪_{X ×_B Y, (x̄, ȳ)}`. -/
def torOneTensorStalk (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    ModuleCat (stalkW f g xybar) :=
  (ModuleCat.extendScalars (tensorStalkProductMap f g xybar).toRingHom).obj
    (TensorAction.obj 1)

/-- Unfolding of `torOneTensorStalk` as scalar extension of the canonical tensor-product module `Tor_1`. -/
theorem torOneTensorStalk_eq (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    torOneTensorStalk f g xybar =
      (ModuleCat.extendScalars (tensorStalkProductMap f g xybar).toRingHom).obj
        (TensorAction.obj 1) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.FibreProduct
