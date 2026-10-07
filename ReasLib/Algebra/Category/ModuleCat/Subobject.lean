module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# Explicit ModuleCat Subobjects

Small bridges between a submodule and its canonical categorical subobject presentation.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- Categorical subobjects of an `R`-module form a complete lattice, transported from the
complete lattice of its submodules. This low-priority instance is a fallback when Mathlib's
generic categorical construction is unavailable at the required universe of coproducts. -/
@[instance 100, stacks 012J "complete lattice of ModuleCat subobjects"]
noncomputable instance subobjectCompleteLattice (M : ModuleCat R) :
    CompleteLattice (Subobject M) :=
  (subobjectModule M).toEquiv.completeLattice

/-- The inverse of `subobjectModule` sends a submodule to the subobject represented by its
subtype inclusion. -/
theorem subobjectModule_symm_eq_mk (M : ModuleCat R) (S : Submodule R M) :
    (subobjectModule M).symm S = Subobject.mk (ofHom S.subtype) := by
  apply (subobjectModule M).injective
  simp [subobjectModule]

namespace SubobjectModule

/-- The underlying object of the categorical subobject represented by a submodule is canonically
the module carried by that submodule. -/
@[stacks 012J "underlying object of a submodule subobject"]
noncomputable def underlyingIso (M : ModuleCat R) (S : Submodule R M) :
    Subobject.underlying.obj ((subobjectModule M).symm S) ≅ of R S :=
  (eqToIso <| congrArg (fun T : Subobject M => (T : ModuleCat R))
    (subobjectModule_symm_eq_mk M S)).trans <|
    @Subobject.underlyingIso _ _ _ _ (ofHom S.subtype)
      (ModuleCat.mono_as_hom'_subtype (X := M) S)

end SubobjectModule

end ModuleCat
