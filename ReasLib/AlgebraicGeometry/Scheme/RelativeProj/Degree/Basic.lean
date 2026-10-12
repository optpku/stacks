/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra

/-!
# Degreewise relative projective-spectrum functors

This leaf owns the functor-of-points data used by degreewise relative `Proj`
constructions.  The graded-algebra pullback datum and its base-change
comparison are kept in separate leaves.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S S' : Scheme.{u}}
variable {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf}
variable {d : ℕ}

/-- Data for a degree-`d` relative projective-spectrum functor of a graded algebra sheaf over a
scheme. -/
structure RelativeProjDegreeFunctor
    (S : Scheme.{u}) (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) (d : ℕ) where
  /-- The positive degree used by the construction. -/
  degree_pos : 1 ≤ d
  /-- The graded algebra is quasi-coherent in every degree. -/
  algebra_isQuasicoherent : ∀ n : ℤ, (𝒜 n).IsQuasicoherent
  /-- The functor on test schemes. -/
  toFunctor : Schemeᵒᵖ ⥤ Type u
  /-- The structural map from the functor to the functor of points of the base scheme. -/
  baseMap : toFunctor ⟶ yoneda.obj S
  /-- Relative projective-spectrum data over a point of the base functor. -/
  pointOver : ∀ (T : Schemeᵒᵖ), (yoneda.obj S).obj T → Type u
  /-- Each functor value is identified with a base point and data over that point. -/
  objIso : ∀ T : Schemeᵒᵖ, toFunctor.obj T ≃ Σ t : (yoneda.obj S).obj T, pointOver T t
  /-- The first component of `objIso` is the structural map to the base. -/
  objIso_hom_base : ∀ (T : Schemeᵒᵖ) (x : toFunctor.obj T),
    (objIso T x).1 = baseMap.app T x
  /-- Reconstructing a functor point from a base point recovers that base point. -/
  objIso_inv_base : ∀ (T : Schemeᵒᵖ) (x : Σ t : (yoneda.obj S).obj T, pointOver T t),
    baseMap.app T ((objIso T).symm x) = x.1

/-- The fiber-product type underlying the base change of a degreewise relative projective-spectrum
functor. -/
def relativeProjDegreeBaseChangeObj
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (T : Schemeᵒᵖ) : Type u :=
  { x : (yoneda.obj S').obj T × F_d.toFunctor.obj T //
      x.1 ≫ g = F_d.baseMap.app T x.2 }

/-- The direct-scheme form of a base-change point of a degreewise relative projective-spectrum
functor. -/
abbrev relativeProjDegreeBaseChangePoint
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (T : Scheme.{u}) : Type u :=
  relativeProjDegreeBaseChangeObj g F_d (Opposite.op T)

/-- The action on base-change points induced by a morphism of test schemes. -/
theorem relativeProjDegreeBaseChangeFunctorMap_property
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    {T T' : Schemeᵒᵖ} (a : T ⟶ T')
    (x : relativeProjDegreeBaseChangeObj g F_d T) :
    (yoneda.obj S').map a x.1.1 ≫ g =
      F_d.baseMap.app T' ((F_d.toFunctor.map a) x.1.2) := sorry

/-- The raw function on base-change points induced by a morphism of test schemes. -/
def relativeProjDegreeBaseChangeFunctorMap
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    {T T' : Schemeᵒᵖ} (a : T ⟶ T') :
    relativeProjDegreeBaseChangeObj g F_d T → relativeProjDegreeBaseChangeObj g F_d T' :=
  fun x ↦
    ⟨⟨(yoneda.obj S').map a x.1.1, (F_d.toFunctor.map a) x.1.2⟩,
      relativeProjDegreeBaseChangeFunctorMap_property g F_d a x⟩

/-- The raw base-change point map respects identities. -/
theorem relativeProjDegreeBaseChangeFunctorMap_id
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d) (T : Schemeᵒᵖ) :
    relativeProjDegreeBaseChangeFunctorMap g F_d (𝟙 T) =
      id := sorry

/-- The raw base-change point map respects composition. -/
theorem relativeProjDegreeBaseChangeFunctorMap_comp
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    {T T' T'' : Schemeᵒᵖ} (a : T ⟶ T') (b : T' ⟶ T'') :
    relativeProjDegreeBaseChangeFunctorMap g F_d (a ≫ b) =
      relativeProjDegreeBaseChangeFunctorMap g F_d b ∘
        relativeProjDegreeBaseChangeFunctorMap g F_d a := sorry

/-- The identity law for the base-change point map as a morphism in the category of types. -/
theorem relativeProjDegreeBaseChangeFunctorMap_id_hom
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d) (T : Schemeᵒᵖ) :
    TypeCat.ofHom (relativeProjDegreeBaseChangeFunctorMap g F_d (𝟙 T)) =
      𝟙 (relativeProjDegreeBaseChangeObj g F_d T) := sorry

/-- The composition law for the base-change point map as a morphism in the category of types. -/
theorem relativeProjDegreeBaseChangeFunctorMap_comp_hom
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    {T T' T'' : Schemeᵒᵖ} (a : T ⟶ T') (b : T' ⟶ T'') :
    TypeCat.ofHom (relativeProjDegreeBaseChangeFunctorMap g F_d (a ≫ b)) =
      TypeCat.ofHom (relativeProjDegreeBaseChangeFunctorMap g F_d a) ≫
        TypeCat.ofHom (relativeProjDegreeBaseChangeFunctorMap g F_d b) := sorry

/-- The functor of points obtained by base-changing a degreewise relative projective-spectrum
functor. -/
def relativeProjDegreeBaseChangeFunctor
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d) :
    Schemeᵒᵖ ⥤ Type u where
  obj := relativeProjDegreeBaseChangeObj g F_d
  map a := TypeCat.ofHom (relativeProjDegreeBaseChangeFunctorMap g F_d a)
  map_id T := relativeProjDegreeBaseChangeFunctorMap_id_hom g F_d T
  map_comp a b := relativeProjDegreeBaseChangeFunctorMap_comp_hom g F_d a b

/-- The forward raw point map induced by a family of equivalences between relative
projective-spectrum data after base change. -/
def relativeProjDegreeFunctorBaseChangeIsoHomAppOfEquiv
    (g : S' ⟶ S) (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (𝒜' : GradedAlgebraSheaf.{u, u} S'.sheaf)
    (F'_d : RelativeProjDegreeFunctor S' 𝒜' d)
    (homEquiv : ∀ (T : Schemeᵒᵖ) (t : (yoneda.obj S').obj T),
      F'_d.pointOver T t ≃ F_d.pointOver T (t ≫ g))
    (T : Schemeᵒᵖ) :
    F'_d.toFunctor.obj T → relativeProjDegreeBaseChangeObj g F_d T :=
  fun x ↦
    let x' := F'_d.objIso T x
    let y : F_d.toFunctor.obj T :=
      (F_d.objIso T).symm ⟨x'.1 ≫ g, homEquiv T x'.1 x'.2⟩
    ⟨⟨x'.1, y⟩,
      (F_d.objIso_inv_base T ⟨x'.1 ≫ g, homEquiv T x'.1 x'.2⟩).symm⟩

end AlgebraicGeometry.Scheme
