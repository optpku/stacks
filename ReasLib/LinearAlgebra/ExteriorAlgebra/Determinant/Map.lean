/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.Basic
public import ReasLib.LinearAlgebra.ExteriorAlgebra.Equiv
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of determinant submodules

@stack 0FJB

An equivalence of modules acts on determinant submodules through the induced exterior-algebra
map.  No finiteness, projectivity, or rank assumptions are needed.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped Module.Determinant

namespace Module.Determinant

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- An exterior-algebra map induced by a module equivalence carries determinant elements to
determinant elements. -/
@[stacks 0FJB "determinant elements are preserved by equivalences"]
theorem map_mem (e : M ≃ₗ[R] N) (x : det[R](M)) :
    ExteriorAlgebra.map e.toLinearMap (x : ExteriorAlgebra R M) ∈ det[R](N) := sorry

/-- The forward map on determinant submodules induced by a module equivalence. -/
@[stacks 0FJB "forward map on determinant submodules"]
def mapIsoHom (e : M ≃ₗ[R] N) : det[R](M) →ₗ[R] det[R](N) :=
  LinearMap.codRestrict det[R](N)
    ((ExteriorAlgebra.map e.toLinearMap).toLinearMap.comp (ι R M))
    (map_mem e)

/-- The forward determinant map is induced by the corresponding exterior-algebra map. -/
@[stacks 0FJB "forward determinant map inclusion equation"]
theorem mapIsoHom_ι (e : M ≃ₗ[R] N) :
    (ι R N).comp (mapIsoHom e) =
      (ExteriorAlgebra.map e.toLinearMap).toLinearMap.comp (ι R M) := sorry

/-- The inverse map on determinant submodules induced by a module equivalence. -/
@[stacks 0FJB "inverse map on determinant submodules"]
def mapIsoInv (e : M ≃ₗ[R] N) : det[R](N) →ₗ[R] det[R](M) :=
  mapIsoHom e.symm

/-- The inverse determinant map is induced by the inverse exterior-algebra map. -/
@[stacks 0FJB "inverse determinant map inclusion equation"]
theorem mapIsoInv_ι (e : M ≃ₗ[R] N) :
    (ι R M).comp (mapIsoInv e) =
      (ExteriorAlgebra.map e.symm.toLinearMap).toLinearMap.comp (ι R N) := sorry

/-- The forward determinant map followed by its inverse is the identity. -/
@[stacks 0FJB "forward-inverse determinant map identity"]
theorem mapIsoHom_comp_mapIsoInv (e : M ≃ₗ[R] N) :
    (mapIsoHom e).comp (mapIsoInv e) = LinearMap.id := sorry

/-- The inverse determinant map followed by the forward map is the identity. -/
@[stacks 0FJB "inverse-forward determinant map identity"]
theorem mapIsoInv_comp_mapIsoHom (e : M ≃ₗ[R] N) :
    (mapIsoInv e).comp (mapIsoHom e) = LinearMap.id := sorry

/-- A module equivalence induces a canonical equivalence of determinant submodules. -/
@[stacks 0FJB "determinant equivalence induced by a module equivalence"]
def mapIso (e : M ≃ₗ[R] N) : det[R](M) ≃ₗ[R] det[R](N) :=
  LinearEquiv.ofLinear
    (mapIsoHom e)
    (mapIsoInv e)
    (mapIsoHom_comp_mapIsoInv e)
    (mapIsoInv_comp_mapIsoHom e)

/-- The forward map of the determinant equivalence is `mapIsoHom`. -/
@[simp, stacks 0FJB "determinant equivalence forward map"]
theorem mapIso_toLinearMap (e : M ≃ₗ[R] N) :
    (mapIso e).toLinearMap = mapIsoHom e := sorry

/-- The determinant equivalence commutes with the inclusions into exterior algebras. -/
@[stacks 0FJB "determinant equivalence inclusion equation"]
theorem mapIso_ι (e : M ≃ₗ[R] N) :
    (ι R N).comp (mapIso e).toLinearMap =
      (ExteriorAlgebra.map e.toLinearMap).toLinearMap.comp (ι R M) := sorry

/-- The inverse module equivalence induces the inverse determinant equivalence. -/
@[simp, stacks 0FJB "determinant equivalence under symmetry"]
theorem mapIso_symm (e : M ≃ₗ[R] N) :
    mapIso e.symm = (mapIso e).symm := sorry

/-- The identity module equivalence induces the identity determinant equivalence. -/
@[simp, stacks 0FJB "determinant equivalence of the identity"]
theorem mapIso_refl :
    mapIso (LinearEquiv.refl R M) = LinearEquiv.refl R det[R](M) := sorry

/-- Determinant equivalences respect composition of module equivalences. -/
@[simp, stacks 0FJB "composition of determinant equivalences"]
theorem mapIso_trans {P : Type*} [AddCommGroup P] [Module R P]
    (e : M ≃ₗ[R] N) (e' : N ≃ₗ[R] P) :
    mapIso (e.trans e') = (mapIso e).trans (mapIso e') := sorry

end Module.Determinant
