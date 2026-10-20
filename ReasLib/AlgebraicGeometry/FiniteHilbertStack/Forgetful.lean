module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Hom.Construction
public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Base

/-!
# Forgetful 1-morphisms of finite Hilbert stacks

The four natural forgetful 1-morphisms of stacks in groupoids over `(Sch/S)_fppf`
associated with `H_d(𝒳)`, `H_d(𝒳/𝒴)`, `H_d`, and `𝒴`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open FiberedCategoryOver.Groupoids
open StackOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- Replace `(y, α)` by the canonical base-fibre data of `H_d(𝒳) = H_d(𝒳/S)`. -/
def forgetToAbsoluteObj (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    (ξ : Obj (asGroupoidsOverMor F) d) :
    Obj (toSchemeProjection 𝒳) d :=
  Obj.of ξ.U ξ.Z ξ.π ξ.finiteLocallyFree (baseFiber ξ.U) ξ.x (ofStackIso ξ.π ξ.x)

/-- The canonical base-fibre comparisons preserve the compatibility square of finite Hilbert morphisms. -/
theorem forgetToAbsoluteMap_comm (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {ξ ξ' : Obj (asGroupoidsOverMor F) d} (φ : Hom ξ ξ') :
    HomCompatible (ξ := forgetToAbsoluteObj F d ξ) (ξ' := forgetToAbsoluteObj F d ξ')
      φ.f φ.g φ.over_comm (baseRestrictIso φ.f).symm φ.a :=
  sorry

/-- Keep `(f, g, a)` and insert the canonical base-fibre isomorphism `b`. -/
def forgetToAbsoluteMap (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {ξ ξ' : Obj (asGroupoidsOverMor F) d} (φ : Hom ξ ξ') :
    Hom (forgetToAbsoluteObj F d ξ) (forgetToAbsoluteObj F d ξ') :=
  { f := φ.f
    g := φ.g
    over_comm := φ.over_comm
    isPullback := φ.isPullback
    b := (baseRestrictIso φ.f).symm
    a := φ.a
    comm := forgetToAbsoluteMap_comm F d φ }

/-- The forgetful morphism operation preserves the identity of each finite Hilbert object. -/
theorem forgetToAbsoluteMap_id (F : 𝒳 ⟶ 𝒴) (d : ℕ) (ξ : Obj (asGroupoidsOverMor F) d) :
    forgetToAbsoluteMap F d (𝟙 ξ) = 𝟙 (forgetToAbsoluteObj F d ξ) :=
  sorry

/-- The forgetful morphism operation preserves composition in the finite Hilbert category. -/
theorem forgetToAbsoluteMap_comp (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {ξ ξ' ξ'' : Obj (asGroupoidsOverMor F) d} (φ : ξ ⟶ ξ') (ψ : ξ' ⟶ ξ'') :
    forgetToAbsoluteMap F d (φ ≫ ψ) =
      CategoryStruct.comp (obj := Obj (toSchemeProjection 𝒳) d)
        (forgetToAbsoluteMap F d φ) (forgetToAbsoluteMap F d ψ) :=
  sorry

/-- The total functor of `H_d(𝒳/𝒴) ⟶ H_d(𝒳)`. -/
def forgetToAbsoluteFunctor (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    Obj (asGroupoidsOverMor F) d ⥤
      Obj (toSchemeProjection 𝒳) d where
  obj := forgetToAbsoluteObj F d
  map := forgetToAbsoluteMap F d
  map_id := forgetToAbsoluteMap_id F d
  map_comp := forgetToAbsoluteMap_comp F d

/-- The forgetful functor `H_d(𝒳/𝒴) ⟶ H_d(𝒳)` lies over `(Sch/S)_fppf`. -/
theorem forgetToAbsoluteFunctor_w (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    forgetToAbsoluteFunctor F d ⋙ (ofStack (asGroupoidsOver 𝒳) d).p =
      (stack (asGroupoidsOverMor F) d).p :=
  sorry

/-- The based forgetful functor `H_d(𝒳/𝒴) ⟶ H_d(𝒳)`. -/
def forgetToAbsoluteBased (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    (stack (asGroupoidsOverMor F) d).toBasedCategory ⥤ᵇ
      (ofStack (asGroupoidsOver 𝒳) d).toBasedCategory where
  toFunctor := forgetToAbsoluteFunctor F d
  w := forgetToAbsoluteFunctor_w F d

/-- The forgetful 1-morphism `H_d(𝒳/𝒴) ⟶ H_d(𝒳)` of stacks in groupoids. -/
def forgetToAbsolute (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    stack (asGroupoidsOverMor F) d ⟶ ofStack (asGroupoidsOver 𝒳) d :=
  lift (ofBasedFunctor (forgetToAbsoluteBased F d))

/-- The object map of `forgetToAbsolute` keeps `(U, Z, x)` and inserts `y_S, α_S`. -/
theorem forgetToAbsolute_obj (F : 𝒳 ⟶ 𝒴) (d : ℕ) (ξ : Obj (asGroupoidsOverMor F) d) :
    (forgetToAbsoluteFunctor F d).obj ξ = forgetToAbsoluteObj F d ξ :=
  rfl

/-- Send a quintuple to the underlying fibre object `y` of `𝒴`. -/
def forgetToYObj (F : 𝒳 ⟶ 𝒴) (d : ℕ) (ξ : Obj (asGroupoidsOverMor F) d) : 𝒴.total :=
  ξ.y.1

/-- Send `(f, g, b, a)` to the total morphism of `b` over `f`. -/
def forgetToYMap (F : 𝒳 ⟶ 𝒴) (d : ℕ) {ξ ξ' : Obj (asGroupoidsOverMor F) d} (φ : Hom ξ ξ') :
    forgetToYObj F d ξ ⟶ forgetToYObj F d ξ' :=
  φ.b.hom.1 ≫ IsPreFibered.pullbackMap ξ'.y.property φ.f

/-- The forgetful morphism operation preserves the identity of each finite Hilbert object. -/
theorem forgetToYMap_id (F : 𝒳 ⟶ 𝒴) (d : ℕ) (ξ : Obj (asGroupoidsOverMor F) d) :
    forgetToYMap F d (𝟙 ξ) = 𝟙 (forgetToYObj F d ξ) :=
  sorry

/-- The forgetful morphism operation preserves composition in the finite Hilbert category. -/
theorem forgetToYMap_comp (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {ξ ξ' ξ'' : Obj (asGroupoidsOverMor F) d} (φ : ξ ⟶ ξ') (ψ : ξ' ⟶ ξ'') :
    forgetToYMap F d (φ ≫ ψ) = forgetToYMap F d φ ≫ forgetToYMap F d ψ :=
  sorry

/-- The total functor of `H_d(𝒳/𝒴) ⟶ 𝒴`. -/
def forgetToYFunctor (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    Obj (asGroupoidsOverMor F) d ⥤ 𝒴.total where
  obj := forgetToYObj F d
  map := forgetToYMap F d
  map_id := forgetToYMap_id F d
  map_comp := forgetToYMap_comp F d

/-- The forgetful functor `H_d(𝒳/𝒴) ⟶ 𝒴` lies over `(Sch/S)_fppf`. -/
theorem forgetToYFunctor_w (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    forgetToYFunctor F d ⋙ 𝒴.p = (stack (asGroupoidsOverMor F) d).p :=
  sorry

/-- The based forgetful functor `H_d(𝒳/𝒴) ⟶ 𝒴`. -/
def forgetToYBased (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    (stack (asGroupoidsOverMor F) d).toBasedCategory ⥤ᵇ 𝒴.toBasedCategory where
  toFunctor := forgetToYFunctor F d
  w := forgetToYFunctor_w F d

/-- The forgetful 1-morphism `H_d(𝒳/𝒴) ⟶ 𝒴` of stacks in groupoids. -/
def forgetToY (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    stack (asGroupoidsOverMor F) d ⟶ 𝒴 :=
  lift (ofBasedFunctor (forgetToYBased F d))

/-- The object map of `forgetToY` is the fibre object `y`. -/
theorem forgetToY_obj (F : 𝒳 ⟶ 𝒴) (d : ℕ) (ξ : Obj (asGroupoidsOverMor F) d) :
    (forgetToYFunctor F d).obj ξ = ξ.y.1 :=
  rfl

/-- Replace `(y, x, α)` by the canonical base-fibre data of `H_d = H_d(S/S)`. -/
def forgetToPointObj (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    (ξ : Obj (asGroupoidsOverMor F) d) :
    Obj (𝟙 (schemeBase S)) d :=
  Obj.of ξ.U ξ.Z ξ.π ξ.finiteLocallyFree (baseFiber ξ.U) (baseFiber ξ.Z) (ofSchemeIso ξ.π)

/-- The canonical base-fibre comparisons preserve the compatibility square of finite Hilbert morphisms. -/
theorem forgetToPointMap_comm (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {ξ ξ' : Obj (asGroupoidsOverMor F) d} (φ : Hom ξ ξ') :
    HomCompatible (ξ := forgetToPointObj F d ξ) (ξ' := forgetToPointObj F d ξ')
      φ.f φ.g φ.over_comm (baseRestrictIso φ.f).symm (baseRestrictIso φ.g).symm :=
  sorry

/-- Keep `(f, g)` and insert the canonical base-fibre isomorphisms `(b, a)`. -/
def forgetToPointMap (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {ξ ξ' : Obj (asGroupoidsOverMor F) d} (φ : Hom ξ ξ') :
    Hom (forgetToPointObj F d ξ) (forgetToPointObj F d ξ') :=
  { f := φ.f
    g := φ.g
    over_comm := φ.over_comm
    isPullback := φ.isPullback
    b := (baseRestrictIso φ.f).symm
    a := (baseRestrictIso φ.g).symm
    comm := forgetToPointMap_comm F d φ }

/-- The forgetful morphism operation preserves the identity of each finite Hilbert object. -/
theorem forgetToPointMap_id (F : 𝒳 ⟶ 𝒴) (d : ℕ) (ξ : Obj (asGroupoidsOverMor F) d) :
    forgetToPointMap F d (𝟙 ξ) = 𝟙 (forgetToPointObj F d ξ) :=
  sorry

/-- The forgetful morphism operation preserves composition in the finite Hilbert category. -/
theorem forgetToPointMap_comp (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    {ξ ξ' ξ'' : Obj (asGroupoidsOverMor F) d} (φ : ξ ⟶ ξ') (ψ : ξ' ⟶ ξ'') :
    forgetToPointMap F d (φ ≫ ψ) =
      CategoryStruct.comp (obj := Obj (𝟙 (schemeBase S)) d)
        (forgetToPointMap F d φ) (forgetToPointMap F d ψ) :=
  sorry

/-- The total functor of `H_d(𝒳/𝒴) ⟶ H_d`. -/
def forgetToPointFunctor (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    Obj (asGroupoidsOverMor F) d ⥤ Obj (𝟙 (schemeBase S)) d where
  obj := forgetToPointObj F d
  map := forgetToPointMap F d
  map_id := forgetToPointMap_id F d
  map_comp := forgetToPointMap_comp F d

/-- The forgetful functor `H_d(𝒳/𝒴) ⟶ H_d` lies over `(Sch/S)_fppf`. -/
theorem forgetToPointFunctor_w (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    forgetToPointFunctor F d ⋙ (ofScheme S d).p = (stack (asGroupoidsOverMor F) d).p :=
  sorry

/-- The based forgetful functor `H_d(𝒳/𝒴) ⟶ H_d`. -/
def forgetToPointBased (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    (stack (asGroupoidsOverMor F) d).toBasedCategory ⥤ᵇ
      (ofScheme S d).toBasedCategory where
  toFunctor := forgetToPointFunctor F d
  w := forgetToPointFunctor_w F d

/-- The forgetful 1-morphism `H_d(𝒳/𝒴) ⟶ H_d` of stacks in groupoids. -/
def forgetToPoint (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    stack (asGroupoidsOverMor F) d ⟶ ofScheme S d :=
  lift (ofBasedFunctor (forgetToPointBased F d))

/-- The object map of `forgetToPoint` keeps `(U, Z)` and inserts canonical base data. -/
theorem forgetToPoint_obj (F : 𝒳 ⟶ 𝒴) (d : ℕ) (ξ : Obj (asGroupoidsOverMor F) d) :
    (forgetToPointFunctor F d).obj ξ = forgetToPointObj F d ξ :=
  rfl

/-- Replace `x` by the canonical base-fibre object of `H_d`. -/
def absoluteToPointObj
    (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ)
    (ξ : Obj (toSchemeProjection 𝒳) d) :
    Obj (𝟙 (schemeBase S)) d :=
  Obj.of ξ.U ξ.Z ξ.π ξ.finiteLocallyFree (baseFiber ξ.U) (baseFiber ξ.Z) (ofSchemeIso ξ.π)

/-- The canonical base-fibre comparisons preserve the compatibility square of finite Hilbert morphisms. -/
theorem absoluteToPointMap_comm (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ)
    {ξ ξ' : Obj (toSchemeProjection 𝒳) d} (φ : Hom ξ ξ') :
    HomCompatible (ξ := absoluteToPointObj 𝒳 d ξ) (ξ' := absoluteToPointObj 𝒳 d ξ')
      φ.f φ.g φ.over_comm (baseRestrictIso φ.f).symm (baseRestrictIso φ.g).symm :=
  sorry

/-- Keep `(f, g)` and insert the canonical base-fibre isomorphisms `(b, a)`. -/
def absoluteToPointMap
    (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ)
    {ξ ξ' : Obj (toSchemeProjection 𝒳) d} (φ : Hom ξ ξ') :
    Hom (absoluteToPointObj 𝒳 d ξ) (absoluteToPointObj 𝒳 d ξ') :=
  { f := φ.f
    g := φ.g
    over_comm := φ.over_comm
    isPullback := φ.isPullback
    b := (baseRestrictIso φ.f).symm
    a := (baseRestrictIso φ.g).symm
    comm := absoluteToPointMap_comm 𝒳 d φ }

/-- The forgetful morphism operation preserves the identity of each finite Hilbert object. -/
theorem absoluteToPointMap_id (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ) (ξ : Obj (toSchemeProjection 𝒳) d) :
    absoluteToPointMap 𝒳 d (𝟙 ξ) = 𝟙 (absoluteToPointObj 𝒳 d ξ) :=
  sorry

/-- The forgetful morphism operation preserves composition in the finite Hilbert category. -/
theorem absoluteToPointMap_comp (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ)
    {ξ ξ' ξ'' : Obj (toSchemeProjection 𝒳) d} (φ : ξ ⟶ ξ') (ψ : ξ' ⟶ ξ'') :
    absoluteToPointMap 𝒳 d (φ ≫ ψ) =
      CategoryStruct.comp (obj := Obj (𝟙 (schemeBase S)) d)
        (absoluteToPointMap 𝒳 d φ) (absoluteToPointMap 𝒳 d ψ) :=
  sorry

/-- The total functor of `H_d(𝒳) ⟶ H_d`. -/
def absoluteToPointFunctor
    (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ) :
    Obj (toSchemeProjection 𝒳) d ⥤
      Obj (𝟙 (schemeBase S)) d where
  obj := absoluteToPointObj 𝒳 d
  map := absoluteToPointMap 𝒳 d
  map_id := absoluteToPointMap_id 𝒳 d
  map_comp := absoluteToPointMap_comp 𝒳 d

/-- The forgetful functor `H_d(𝒳) ⟶ H_d` lies over `(Sch/S)_fppf`. -/
theorem absoluteToPointFunctor_w
    (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ) :
    absoluteToPointFunctor 𝒳 d ⋙ (ofScheme S d).p = (ofStack (asGroupoidsOver 𝒳) d).p :=
  sorry

/-- The based forgetful functor `H_d(𝒳) ⟶ H_d`. -/
def absoluteToPointBased
    (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ) :
    (ofStack (asGroupoidsOver 𝒳) d).toBasedCategory ⥤ᵇ
      (ofScheme S d).toBasedCategory where
  toFunctor := absoluteToPointFunctor 𝒳 d
  w := absoluteToPointFunctor_w 𝒳 d

/-- The forgetful 1-morphism `H_d(𝒳) ⟶ H_d` of stacks in groupoids. -/
def absoluteToPoint
    (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ) :
    ofStack (asGroupoidsOver 𝒳) d ⟶ ofScheme S d :=
  lift (ofBasedFunctor (absoluteToPointBased 𝒳 d))

/-- The object map of `absoluteToPoint` keeps `(U, Z)` and inserts canonical base data. -/
theorem absoluteToPoint_obj
    (𝒳 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)) (d : ℕ)
    (ξ : Obj (toSchemeProjection 𝒳) d) :
    (absoluteToPointFunctor 𝒳 d).obj ξ = absoluteToPointObj 𝒳 d ξ :=
  rfl

/-- The triangle `H_d(𝒳/𝒴) ⟶ H_d(𝒳) ⟶ H_d` agrees with `H_d(𝒳/𝒴) ⟶ H_d`. -/
theorem forgetToAbsolute_comp_absoluteToPoint (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    forgetToAbsolute F d ≫ absoluteToPoint 𝒳 d = forgetToPoint F d :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
