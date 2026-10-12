/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap95.Definition_95_18_2
public import stacks_project.Chap95.«95_18_2_1_Forgetful»

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

namespace AlgebraicGeometry

/-- A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` commutes with
the canonical projections to the identity fibration. -/
theorem comp_baseProjection {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    f ≫ baseProjection.{u + 1, u, u + 1} Y = baseProjection.{u + 1, u, u + 1} X :=
  sorry

/-- The pairing of `f : U ⟶ X` and `g : U ⟶ Y` as a pseudo-pullback cone over the
cospan of `baseProjection` morphisms. -/
def pairOverBaseCone {S : Scheme.{u}} {X Y U : GroupoidsOver S} (f : U ⟶ X) (g : U ⟶ Y) :
    PseudoPullbackCone (baseProjection.{u + 1, u, u + 1} X)
      (baseProjection.{u + 1, u, u + 1} Y) where
  pt := U
  fst := f
  snd := g
  iso := eqToIso (comp_baseProjection f) ≪≫ (eqToIso (comp_baseProjection g)).symm

/-- The 1-morphism `U ⟶ X × Y` induced by a pair of 1-morphisms with common source,
where `X × Y` is the 2-fibre product of the two `baseProjection` morphisms. -/
noncomputable def pairOverBase {S : Scheme.{u}} {X Y U : GroupoidsOver S}
    (f : U ⟶ X) (g : U ⟶ Y) :
    U ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (baseProjection.{u + 1, u, u + 1} X)
        (baseProjection.{u + 1, u, u + 1} Y) :=
  PseudoPullbackCone.lift (pairOverBaseCone f g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} X)
      (baseProjection.{u + 1, u, u + 1} Y))

/-- The first projection of `pairOverBase f g` is isomorphic to `f`. -/
noncomputable def pairOverBase_fst {S : Scheme.{u}} {X Y U : GroupoidsOver S}
    (f : U ⟶ X) (g : U ⟶ Y) :
    pairOverBase f g ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u}
          (baseProjection.{u + 1, u, u + 1} X)
          (baseProjection.{u + 1, u, u + 1} Y) ≅
      f :=
  PseudoPullbackCone.lift.fstIso (pairOverBaseCone f g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} X)
      (baseProjection.{u + 1, u, u + 1} Y))

/-- The second projection of `pairOverBase f g` is isomorphic to `g`. -/
noncomputable def pairOverBase_snd {S : Scheme.{u}} {X Y U : GroupoidsOver S}
    (f : U ⟶ X) (g : U ⟶ Y) :
    pairOverBase f g ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u}
          (baseProjection.{u + 1, u, u + 1} X)
          (baseProjection.{u + 1, u, u + 1} Y) ≅
      g :=
  PseudoPullbackCone.lift.sndIso (pairOverBaseCone f g)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (baseProjection.{u + 1, u, u + 1} X)
      (baseProjection.{u + 1, u, u + 1} Y))

/-- `pairOverBase` is the universal lift of `pairOverBaseCone` into the 2-fibre
product of the two `baseProjection` morphisms. -/
theorem pairOverBase_eq {S : Scheme.{u}} {X Y U : GroupoidsOver S}
    (f : U ⟶ X) (g : U ⟶ Y) :
    pairOverBase f g =
      PseudoPullbackCone.lift (pairOverBaseCone f g)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
          (baseProjection.{u + 1, u, u + 1} X)
          (baseProjection.{u + 1, u, u + 1} Y)) :=
  sorry

namespace FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- 97.12.5.1: the 2-fibre product
`(Sch/U)_fppf ×_{ξ × y, ℋ_d(𝒳) × 𝒴} ℋ_d(𝒳/𝒴)`.
`GroupoidsOver.slice U` is `(Sch/U)_fppf`; `ξ` is an object of `ℋ_d(𝒳)` over `U`
and `y` is an object of `𝒴` over `U`, represented as 1-morphisms by
`YonedaSlice.representative`; the product `ℋ_d(𝒳) × 𝒴` is the 2-fibre product of
the two `baseProjection` morphisms; `ξ × y` is `pairOverBase` of those
representatives; and the second leg is `pairOverBase` of the forgetful
1-morphisms `forgetToAbsolute F d` and `forgetToY F d`. -/
@[stacks 05YI]
noncomputable def relativeResIsom (F : 𝒳 ⟶ 𝒴) (d : ℕ) {U : Over S}
    (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U)
    (y : (asGroupoidsOver 𝒴).p.Fiber U) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u}
    (pairOverBase (YonedaSlice.representative ξ) (YonedaSlice.representative y))
    (pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d))
      (asGroupoidsOverMor (forgetToY F d)))

/-- `relativeResIsom` is the 2-fibre product of `ξ × y` with the forgetful map
`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴`. -/
theorem relativeResIsom_eq (F : 𝒳 ⟶ 𝒴) (d : ℕ) {U : Over S}
    (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U)
    (y : (asGroupoidsOver 𝒴).p.Fiber U) :
    relativeResIsom F d ξ y =
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (pairOverBase (YonedaSlice.representative ξ) (YonedaSlice.representative y))
        (pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d))
          (asGroupoidsOverMor (forgetToY F d))) :=
  sorry

/-- The displayed object is the apex of the canonical 2-fibre-product cone of
`ξ × y` and the forgetful map `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴`. -/
theorem relativeResIsom_spec (F : 𝒳 ⟶ 𝒴) (d : ℕ) {U : Over S}
    (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U)
    (y : (asGroupoidsOver 𝒴).p.Fiber U) :
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
        (pairOverBase (YonedaSlice.representative ξ) (YonedaSlice.representative y))
        (pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d))
          (asGroupoidsOverMor (forgetToY F d)))).pt =
      relativeResIsom F d ξ y :=
  sorry

/-- First projection of the displayed 2-fibre product, to `(Sch/U)_fppf`. -/
noncomputable abbrev relativeResIsom.fst (F : 𝒳 ⟶ 𝒴) (d : ℕ) {U : Over S}
    (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U)
    (y : (asGroupoidsOver 𝒴).p.Fiber U) :
    relativeResIsom F d ξ y ⟶ GroupoidsOver.slice U :=
  TwoFibreProduct.fst.{u + 1, u, u + 1, u}
    (pairOverBase (YonedaSlice.representative ξ) (YonedaSlice.representative y))
    (pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d))
      (asGroupoidsOverMor (forgetToY F d)))

/-- Second projection of the displayed 2-fibre product, to `ℋ_d(𝒳/𝒴)`. -/
noncomputable abbrev relativeResIsom.snd (F : 𝒳 ⟶ 𝒴) (d : ℕ) {U : Over S}
    (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U)
    (y : (asGroupoidsOver 𝒴).p.Fiber U) :
    relativeResIsom F d ξ y ⟶ asGroupoidsOver (stack (asGroupoidsOverMor F) d) :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u}
    (pairOverBase (YonedaSlice.representative ξ) (YonedaSlice.representative y))
    (pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d))
      (asGroupoidsOverMor (forgetToY F d)))

end FiniteHilbertStack

end AlgebraicGeometry

