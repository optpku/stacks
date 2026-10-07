module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.Algebra.Category.ModuleCat.Tor.TensorAction
public import stacks_project.Chap92.Lemma_92_28_2_Stalk
public import stacks_project.Chap92.«92_28_0_1_FibreProduct»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology of the fibre-product cotangent cone

Lemma 92.28.2 records the homology of the object `E` of (92.28.0.1): it vanishes in
cohomological degrees `i = 0, -1`, and the stalk of `H^{-2}(E)` at a geometric point of
`X ×_B Y` is `Tor_1` of the étale local rings, base-changed to `𝒪_{X ×_B Y, (x̄, ȳ)}`.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Cotangent
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ModuleCat.Tor
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

/-- Postcomposition of geometric points is strictly functorial. -/
theorem map_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (xbar : GeometricPoint X)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    xbar.map (f ≫ g) = (xbar.map f).map g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint

namespace AlgebraicGeometry.AlgebraicSpace

/-- Transport of étale local rings along equality of geometric points. -/
def etaleLocalRingCongr {S : Scheme.{u}} {X : AlgebraicSpace S} {xbar ybar : GeometricPoint X}
    (h : xbar = ybar) : etaleLocalRing X xbar →+* etaleLocalRing X ybar :=
  h ▸ RingHom.id _

/-- Unfolding of `etaleLocalRingCongr` as transport of the identity ring homomorphism. -/
theorem etaleLocalRingCongr_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {xbar ybar : GeometricPoint X} (h : xbar = ybar) :
    etaleLocalRingCongr h = h ▸ RingHom.id (etaleLocalRing X xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Cotangent
namespace FibreProduct

variable {S : Scheme.{u}}
variable {B X Y : AlgebraicSpace S}

/-- The étale local ring `R = 𝒪_{B, b̄}` at the image of a geometric point of `X ×_B Y`. -/
abbrev stalkBase (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) : Type u :=
  etaleLocalRing B (xybar.map (toBase f g))

/-- Unfolding of `stalkBase` as the étale local ring of `B` at `xybar.map (toBase f g)`. -/
theorem stalkBase_eq (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkBase f g xybar = etaleLocalRing B (xybar.map (toBase f g)) :=
  sorry

/-- The étale local ring `A = 𝒪_{X, x̄}` at the image of a geometric point of `X ×_B Y`. -/
abbrev stalkX (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) : Type u :=
  etaleLocalRing X (xybar.map (pullback.fst f g))

/-- Unfolding of `stalkX` as the étale local ring of `X` at `xybar.map (pullback.fst f g)`. -/
theorem stalkX_eq (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkX f g xybar = etaleLocalRing X (xybar.map (pullback.fst f g)) :=
  sorry

/-- The étale local ring `𝒪_{Y, ȳ}` at the image of a geometric point of `X ×_B Y`. -/
abbrev stalkY (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) : Type u :=
  etaleLocalRing Y (xybar.map (pullback.snd f g))

/-- Unfolding of `stalkY` as the étale local ring of `Y` at `xybar.map (pullback.snd f g)`. -/
theorem stalkY_eq (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkY f g xybar = etaleLocalRing Y (xybar.map (pullback.snd f g)) :=
  sorry

/-- The étale local ring `C = 𝒪_{X ×_B Y, (x̄, ȳ)}` at a geometric point of the fibre product. -/
abbrev stalkW (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) : Type u :=
  etaleLocalRing (pullback f g) xybar

/-- Unfolding of `stalkW` as the étale local ring of `X ×_B Y` at `xybar`. -/
theorem stalkW_eq (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkW f g xybar = etaleLocalRing (pullback f g) xybar :=
  sorry

/-- The local ring map `R →+* A` obtained from `X ⟶ B` after identifying
`xybar.map (toBase f g)` with `(xybar.map (pullback.fst f g)).map f`. -/
def algebraMapStalkBaseStalkX (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    stalkBase f g xybar →+* stalkX f g xybar :=
  (etaleLocalRingMap f (xybar.map (pullback.fst f g))).comp
    (etaleLocalRingCongr (map_comp xybar (pullback.fst f g) f))

/-- Unfolding of `algebraMapStalkBaseStalkX` through `etaleLocalRingMap` and `map_comp`. -/
theorem algebraMapStalkBaseStalkX_eq (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    algebraMapStalkBaseStalkX f g xybar =
      (etaleLocalRingMap f (xybar.map (pullback.fst f g))).comp
        (etaleLocalRingCongr (map_comp xybar (pullback.fst f g) f)) :=
  sorry

/-- The local ring map `R →+* 𝒪_{Y, ȳ}` obtained from `Y ⟶ B` after identifying
`xybar.map (toBase f g)` with `(xybar.map (pullback.snd f g)).map g`. -/
def algebraMapStalkBaseStalkY (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    stalkBase f g xybar →+* stalkY f g xybar :=
  (etaleLocalRingMap g (xybar.map (pullback.snd f g))).comp
    (etaleLocalRingCongr
      ((congrArg (fun h ↦ xybar.map h) pullback.condition).trans
        (map_comp xybar (pullback.snd f g) g)))

/-- Unfolding of `algebraMapStalkBaseStalkY` through `etaleLocalRingMap`, `map_comp`, and
`pullback.condition`. -/
theorem algebraMapStalkBaseStalkY_eq (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    algebraMapStalkBaseStalkY f g xybar =
      (etaleLocalRingMap g (xybar.map (pullback.snd f g))).comp
        (etaleLocalRingCongr
          ((congrArg (fun h ↦ xybar.map h) pullback.condition).trans
            (map_comp xybar (pullback.snd f g) g))) :=
  sorry

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

/-- The `R`-algebra map `A →ₐ[R] C` induced by the projection `X ×_B Y ⟶ X`. -/
def algHomStalkXStalkW (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkX f g xybar →ₐ[stalkBase f g xybar] stalkW f g xybar :=
  { etaleLocalRingMap (pullback.fst f g) xybar with commutes' := sorry }

/-- Unfolding of `algHomStalkXStalkW` as `etaleLocalRingMap` of `pullback.fst`. -/
theorem algHomStalkXStalkW_toRingHom (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    (algHomStalkXStalkW f g xybar).toRingHom =
      etaleLocalRingMap (pullback.fst f g) xybar :=
  sorry

/-- The `R`-algebra map `𝒪_{Y, ȳ} →ₐ[R] C` induced by the projection `X ×_B Y ⟶ Y`. -/
def algHomStalkYStalkW (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    stalkY f g xybar →ₐ[stalkBase f g xybar] stalkW f g xybar :=
  { etaleLocalRingMap (pullback.snd f g) xybar with commutes' := sorry }

/-- Unfolding of `algHomStalkYStalkW` as `etaleLocalRingMap` of `pullback.snd`. -/
theorem algHomStalkYStalkW_toRingHom (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    (algHomStalkYStalkW f g xybar).toRingHom =
      etaleLocalRingMap (pullback.snd f g) xybar :=
  sorry

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
  sorry

/-- The algebra structure on `C` over `A ⊗[R] 𝒪_{Y, ȳ}` induced by the product map. -/
instance instAlgebraTensorStalk (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    Algebra (stalkX f g xybar ⊗[stalkBase f g xybar] stalkY f g xybar)
      (stalkW f g xybar) :=
  (tensorStalkProductMap f g xybar).toAlgebra

/-- `Tor_n^R(A, B)` as a module over `A ⊗[R] B`. -/
abbrev tensorActionObj (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (n : ℕ) : ModuleCat (A ⊗[R] B) :=
  TensorAction.obj n

/-- Unfolding of `tensorActionObj` as `TensorAction.obj`. -/
theorem tensorActionObj_eq (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (n : ℕ) :
    tensorActionObj R A B n = TensorAction.obj n :=
  sorry

/-- `Tor_1^R(A, 𝒪_{Y, ȳ})` base-changed to `C = 𝒪_{X ×_B Y, (x̄, ȳ)}`. -/
def torOneTensorStalk (f : X ⟶ B) (g : Y ⟶ B) (xybar : GeometricPoint (pullback f g)) :
    ModuleCat (stalkW f g xybar) :=
  (ModuleCat.extendScalars (tensorStalkProductMap f g xybar).toRingHom).obj
    (tensorActionObj (stalkBase f g xybar) (stalkX f g xybar) (stalkY f g xybar) 1)

/-- Unfolding of `torOneTensorStalk` as `extendScalars` of `tensorActionObj 1`. -/
theorem torOneTensorStalk_eq (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    torOneTensorStalk f g xybar =
      (ModuleCat.extendScalars (tensorStalkProductMap f g xybar).toRingHom).obj
        (tensorActionObj (stalkBase f g xybar) (stalkX f g xybar)
          (stalkY f g xybar) 1) :=
  sorry

/-- Lemma 92.28.2 (1): for morphisms `X ⟶ B` and `Y ⟶ B` of algebraic spaces over a scheme
`S`, the object `E` in (92.28.0.1) satisfies `H^i(E) = 0` for `i = 0, -1`. -/
@[stacks 09DM]
theorem cone_homology_isZero_of_eq_zero_or_negOne (f : X ⟶ B) (g : Y ⟶ B) {i : ℤ}
    (hi : i = 0 ∨ i = -1) :
    IsZero
      ((DerivedCategory.homologyFunctor (CommModules (pullback f g)) i).obj (cone f g)) :=
  sorry

/-- Lemma 92.28.2 (2): for a geometric point `(x̄, ȳ) : Spec(k) ⟶ X ×_B Y`, the stalk
`H^{-2}(E)_(x̄, ȳ)` is isomorphic to `Tor_1^R(A, 𝒪_{Y, ȳ}) ⊗_{A ⊗[R] 𝒪_{Y, ȳ}} C` as
modules over `C`, where `R = 𝒪_{B, b̄}`, `A = 𝒪_{X, x̄}`, and
`C = 𝒪_{X ×_B Y, (x̄, ȳ)}`. -/
@[stacks 09DM]
theorem cone_homology_negTwo_stalk_isIsomorphic_tor (f : X ⟶ B) (g : Y ⟶ B)
    (xybar : GeometricPoint (pullback f g)) :
    IsIsomorphic
      (commModulesStalk xybar
        ((DerivedCategory.homologyFunctor (CommModules (pullback f g)) (-2)).obj (cone f g)))
      ((ModuleCat.uliftFunctor.{u + 1, u} (stalkW f g xybar)).obj
        (torOneTensorStalk f g xybar)) :=
  sorry

end FibreProduct
end AlgebraicGeometry.AlgebraicSpace.Cotangent
