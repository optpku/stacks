module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Logic.Equiv.Sum
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra

/-!
# Degreewise relative projective-spectrum functors

This leaf owns functors over the functor of points of a base scheme and their
explicit pointwise base changes.
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

/-- A degreewise relative projective-spectrum functor is a functor over the
functor of points of its base, together with positivity and degreewise
quasicoherence. -/
def RelativeProjDegreeFunctor
    (S : Scheme.{u}) (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) (d : ℕ) :=
  { F : CategoryTheory.Over (yoneda.obj S) //
    1 ≤ d ∧ ∀ n : ℤ, (𝒜 n).IsQuasicoherent }

namespace RelativeProjDegreeFunctor

/-- The functor on test schemes underlying a degreewise relative projective-spectrum functor. -/
abbrev toFunctor
    (F_d : RelativeProjDegreeFunctor S 𝒜 d) : Schemeᵒᵖ ⥤ Type u :=
  F_d.1.left

/-- The structural map to the functor of points of the base scheme. -/
abbrev baseMap
    (F_d : RelativeProjDegreeFunctor S 𝒜 d) : F_d.toFunctor ⟶ yoneda.obj S :=
  F_d.1.hom

/-- The degree of a degreewise relative projective-spectrum functor is positive. -/
abbrev degree_pos (F_d : RelativeProjDegreeFunctor S 𝒜 d) : 1 ≤ d :=
  F_d.2.1

/-- Every graded piece of the underlying algebra sheaf is quasicoherent. -/
abbrev algebra_isQuasicoherent
    (F_d : RelativeProjDegreeFunctor S 𝒜 d) (n : ℤ) : (𝒜 n).IsQuasicoherent :=
  F_d.2.2 n

/-- Construct a degreewise relative projective-spectrum functor from a functor,
its structural map, positivity, and degreewise quasicoherence. -/
def ofFunctor
    (toFunctor : Schemeᵒᵖ ⥤ Type u)
    (baseMap : toFunctor ⟶ yoneda.obj S)
    (degree_pos : 1 ≤ d)
    (algebra_isQuasicoherent : ∀ n : ℤ, (𝒜 n).IsQuasicoherent) :
    RelativeProjDegreeFunctor S 𝒜 d :=
  ⟨CategoryTheory.Over.mk baseMap, degree_pos, algebra_isQuasicoherent⟩

/-- The fiber of a degreewise relative projective-spectrum functor over a point
of the base functor. -/
abbrev pointOver
    (F_d : RelativeProjDegreeFunctor S 𝒜 d)
    (T : Schemeᵒᵖ) (t : (yoneda.obj S).obj T) : Type u :=
  { x : F_d.toFunctor.obj T // F_d.baseMap.app T x = t }

/-- A functor value canonically decomposes into its base point and the fiber
over that point. -/
def objIso
    (F_d : RelativeProjDegreeFunctor S 𝒜 d) (T : Schemeᵒᵖ) :
    F_d.toFunctor.obj T ≃ Σ t : (yoneda.obj S).obj T, F_d.pointOver T t :=
  (Equiv.sigmaFiberEquiv (F_d.baseMap.app T)).symm

end RelativeProjDegreeFunctor

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

/-- The forward point map induced by equivalences between the canonical fibers
of two degreewise relative projective-spectrum functors. -/
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
    let y := homEquiv T x'.1 x'.2
    ⟨⟨x'.1, y.1⟩, y.2.symm⟩

end AlgebraicGeometry.Scheme
