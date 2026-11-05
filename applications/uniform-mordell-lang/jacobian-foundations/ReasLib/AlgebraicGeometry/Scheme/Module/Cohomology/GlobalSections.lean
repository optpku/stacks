module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Global-sections modules on scheme cohomology

This leaf gives the canonical module structure on cohomology over the global
section ring, and its restriction along a morphism to an affine scheme.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}


end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}}

/-- Degree-`p` cohomology with scalars restricted along
`f : X ⟶ Spec R`, functorially in the scheme module. -/
noncomputable abbrev cohomologyFunctor
    (f : X ⟶ Spec (CommRingCat.of R)) (p : ℕ) : X.Modules ⥤ ModuleCat R :=
  Scheme.Modules.cohomologyFunctor X p ⋙
    ModuleCat.restrictScalars (globalSectionsMap f)

/-- The degree-`p` cohomology of a scheme module, viewed as an `R`-module by
restriction of scalars along a morphism `f : X ⟶ Spec R`. -/
noncomputable abbrev cohomology
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (p : ℕ) : ModuleCat R :=
  (cohomologyFunctor f p).obj F

/-- Forgetting the affine-base scalar action agrees with forgetting the canonical
`Γ(X, ⊤)`-module structure. -/
@[simp]
theorem cohomology_forget
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (p : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat.{u}).obj (cohomology f F p) =
      (forget₂ (ModuleCat Γ(X, ⊤)) AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology F p) := rfl

/-- Forgetting the affine-base scalar action on `cohomology f F p` recovers
the ordinary cohomology object of the underlying additive sheaf. -/
theorem cohomologyForget_obj_eq
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (p : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat.{u}).obj (cohomology f F p) =
      RingedSpace.moduleCohomology F p := sorry

/-- The dimension of scheme-module cohomology for the canonical scalar action induced by an
affine-base morphism.  This packages the morphism-dependent module datum so numerical clients do
not need to reconstruct a local instance. -/
noncomputable def cohomologyFinrank
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (p : ℕ) : ℕ :=
  Module.finrank R (cohomology f F p)

/-- `cohomologyFinrank` is the ordinary module finrank for the scalar action induced by the
specified affine-base morphism. -/
theorem cohomologyFinrank_def
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (p : ℕ) :
    cohomologyFinrank f F p =
      Module.finrank R (cohomology f F p) := rfl

/-- A coefficient-sheaf isomorphism induces the canonical linear equivalence on cohomology.
The scalar action is the restriction along the specified affine-base morphism `f`.
No properness, coherence, Noetherianity or field assumption is needed. -/
noncomputable def cohomologyLinearEquivOfIso
    (f : X ⟶ Spec (CommRingCat.of R)) {F G : X.Modules} (e : F ≅ G) (p : ℕ) :
    cohomology f F p ≃ₗ[R] cohomology f G p :=
  ((cohomologyFunctor f p).mapIso e).toLinearEquiv

/-- The comparison uses the actual cohomology map of the given sheaf isomorphism. -/
@[simp]
theorem cohomologyLinearEquivOfIso_apply
    (f : X ⟶ Spec (CommRingCat.of R)) {F G : X.Modules} (e : F ≅ G) (p : ℕ)
    (x : cohomology f F p) :
    cohomologyLinearEquivOfIso f e p x = (cohomologyFunctor f p).map e.hom x := rfl

/-- A commutative square of coefficient sheaves gives a commutative square of linear
cohomology comparisons. This records compatibility with maps, beyond equality of dimensions. -/
theorem cohomologyLinearEquivOfIso_naturality
    (f : X ⟶ Spec (CommRingCat.of R)) {F G F' G' : X.Modules}
    (eF : F ≅ F') (eG : G ≅ G') (φ : F ⟶ G) (φ' : F' ⟶ G')
    (h : φ ≫ eG.hom = eF.hom ≫ φ') (p : ℕ) (x : cohomology f F p) :
    cohomologyLinearEquivOfIso f eG p ((cohomologyFunctor f p).map φ x) =
      (cohomologyFunctor f p).map φ' (cohomologyLinearEquivOfIso f eF p x) := by
  have hm := congrArg ((cohomologyFunctor f p).map) h
  simpa only [Functor.map_comp, cohomologyLinearEquivOfIso_apply,
    ModuleCat.comp_apply] using congrArg (fun g => g x) hm

/-- Isomorphic coefficient sheaves have the same finite-generation property over the
affine base. Over a field this is finite-dimensionality. -/
theorem cohomologyFinite_iff_of_iso
    (f : X ⟶ Spec (CommRingCat.of R)) {F G : X.Modules} (e : F ≅ G) (p : ℕ) :
    Module.Finite R (cohomology f F p) ↔ Module.Finite R (cohomology f G p) :=
  ⟨fun _ => Module.Finite.equiv (cohomologyLinearEquivOfIso f e p),
    fun _ => Module.Finite.equiv (cohomologyLinearEquivOfIso f e p).symm⟩

/-- Cohomology dimensions are invariant under coefficient-sheaf isomorphisms. -/
theorem cohomologyFinrank_eq_of_iso
    (f : X ⟶ Spec (CommRingCat.of R)) {F G : X.Modules} (e : F ≅ G) (p : ℕ) :
    cohomologyFinrank f F p = cohomologyFinrank f G p :=
  (cohomologyLinearEquivOfIso f e p).finrank_eq

end AlgebraicGeometry.Scheme.Hom
