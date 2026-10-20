module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Restriction

/-!
# The 1-morphism of finite Hilbert stacks induced by a morphism of sources

A 1-morphism `G : X' ⟶ X` of categories fibred in groupoids induces
`H_d(X'/Y) ⟶ H_d(X/Y)` by applying the fibre functor of `G` to the `X`-component
of a quintuple and composing the comparison isomorphism with `fiberFunctor.comp`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {X' X Y : GroupoidsOver S}

/-- The category fibred in groupoids `H_d(X/Y)` associated to the forgetful
functor `p F d`. -/
abbrev toGroupoids (F : X ⟶ Y) (d : ℕ) : GroupoidsOver S :=
  ofFunctor (p F d)

/-- The projection of `toGroupoids F d` is the forgetful functor `p F d`. -/
theorem toGroupoids_p (F : X ⟶ Y) (d : ℕ) : (toGroupoids F d).p = p F d := sorry

/-- Fibrewise comparison of `G ≫ F` with the composite of the fibre functors of
`G` and `F`. -/
def mapIso (G : X' ⟶ X) (F : X ⟶ Y) {Z : Over S} (x' : X'.p.Fiber Z) :
    (fiberFunctor (G ≫ F) Z).obj x' ≅
      (fiberFunctor F Z).obj ((fiberFunctor G Z).obj x') :=
  eqToIso (congrArg (fun H ↦ H.obj x') (fiberFunctor.comp G F Z))

/-- Object part of the induced 1-morphism: copy `(U, Z, π, y)` and apply the
fibre functor of `G` to `x`. -/
abbrev mapObj (G : X' ⟶ X) (F : X ⟶ Y) {d : ℕ} (ξ : Obj (G ≫ F) d) : Obj F d :=
  Obj.of ξ.U ξ.Z ξ.π ξ.finiteLocallyFree ξ.y ((fiberFunctor G ξ.Z).obj ξ.x)
    (ξ.iso ≪≫ mapIso G F ξ.x)

/-- Morphism part of the induced 1-morphism: the same `(f, g, b)` with `a`
transported by the fibre functor of `G`. -/
def mapHom (G : X' ⟶ X) (F : X ⟶ Y) {d : ℕ} {ξ ξ' : Obj (G ≫ F) d}
    (φ : Hom ξ ξ') : Hom (mapObj G F ξ) (mapObj G F ξ') where
  f := φ.f
  g := φ.g
  over_comm := φ.over_comm
  isPullback := φ.isPullback
  b := φ.b
  a := (fiberFunctor G ξ.Z).mapIso φ.a ≪≫ fiberFunctor_restrictObj G ξ'.x φ.g
  comm := sorry

/-- The induced map on finite Hilbert morphisms preserves identities. -/
theorem mapHom_id (G : X' ⟶ X) (F : X ⟶ Y) {d : ℕ} (ξ : Obj (G ≫ F) d) :
    mapHom G F (𝟙 ξ) = 𝟙 (mapObj G F ξ) := sorry

/-- The induced map on finite Hilbert morphisms preserves composition. -/
theorem mapHom_comp (G : X' ⟶ X) (F : X ⟶ Y) {d : ℕ}
    {ξ ξ' ξ'' : Obj (G ≫ F) d} (φ : ξ ⟶ ξ') (ψ : ξ' ⟶ ξ'') :
    mapHom G F (φ ≫ ψ) = compHom (mapHom G F φ) (mapHom G F ψ) := sorry

/-- The total functor of the induced 1-morphism `H_d(X'/Y) ⟶ H_d(X/Y)`. -/
def mapFunctor (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) : Obj (G ≫ F) d ⥤ Obj F d where
  obj ξ := mapObj G F ξ
  map φ := mapHom G F φ
  map_id := mapHom_id G F
  map_comp := mapHom_comp G F

/-- `mapFunctor` lies strictly over the identity on test schemes. -/
theorem mapFunctor_p (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) :
    mapFunctor G F d ⋙ p F d = p (G ≫ F) d := sorry

/-- The image of a quintuple under `mapFunctor` is obtained by applying the fibre
functor of `G` to the `X`-component and composing with `mapIso`. -/
theorem map_obj (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) (ξ : Obj (G ≫ F) d) :
    (mapFunctor G F d).obj ξ =
      Obj.of ξ.U ξ.Z ξ.π ξ.finiteLocallyFree ξ.y
        ((fiberFunctor G ξ.Z).obj ξ.x) (ξ.iso ≪≫ mapIso G F ξ.x) := sorry

/-- `mapFunctor` preserves the underlying test scheme. -/
theorem map_U (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) (ξ : Obj (G ≫ F) d) :
    ((mapFunctor G F d).obj ξ).U = ξ.U := sorry

/-- The 1-morphism `H_d(X'/Y) ⟶ H_d(X/Y)` of categories fibred in groupoids
induced by `G : X' ⟶ X`. -/
def map (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) :
    toGroupoids (G ≫ F) d ⟶ toGroupoids F d :=
  ofBasedFunctor (BasedFunctor.ofFunctor (mapFunctor G F d) (mapFunctor_p G F d))

/-- Forgetting `map` to based functors recovers `BasedFunctor.ofFunctor` of
`mapFunctor`. -/
theorem map.toBasedFunctor (G : X' ⟶ X) (F : X ⟶ Y) (d : ℕ) :
    toBasedFunctor (map G F d) =
      BasedFunctor.ofFunctor (mapFunctor G F d) (mapFunctor_p G F d) := sorry

end AlgebraicGeometry.FiniteHilbertStack
