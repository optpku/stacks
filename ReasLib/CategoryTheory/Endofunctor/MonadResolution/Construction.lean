/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Endofunctor.MonadResolution.Generators
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical cosimplicial resolutions of monads

This leaf makes the generated resolution canonical: it is functorial in the Mathlib `Monad`,
carries a realization witness, and is canonically isomorphic to every realization of the same
iterated-endofunctor formulas.
-/

@[expose] public section

open CategoryTheory.CosimplicialObject
open CategoryTheory.Functor
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Monad

variable (T : Monad C)

/-- A cosimplicial endofunctor object realizes the iterated resolution formulas of `T`. -/
@[stacks 0G5N "monad cosimplicial resolution realization predicate"]
abbrev Realizes (T : Monad C) (U : CosimplicialObject (C ⥤ C)) : Prop :=
  EndofunctorResolution.CosimplicialRealization T.η T.μ U

/-- The left unit identity in the iterated-endofunctor presentation of a monad. -/
@[stacks 0G5N "monad resolution left unit"]
theorem cosimplicialResolution.left_unit :
    IteratedEndofunctor.coface T.η 0 0 ≫
      IteratedEndofunctor.codegeneracy T.μ 0 0 =
        𝟙 T.toFunctor := sorry

/-- The right unit identity in the iterated-endofunctor presentation of a monad. -/
@[stacks 0G5N "monad resolution right unit"]
theorem cosimplicialResolution.right_unit :
    IteratedEndofunctor.coface T.η 0 1 ≫
      IteratedEndofunctor.codegeneracy T.μ 0 0 =
        𝟙 T.toFunctor := sorry

/-- Associativity in the iterated-endofunctor presentation of a monad. -/
@[stacks 0G5N "monad resolution associativity"]
theorem cosimplicialResolution.assoc :
    IteratedEndofunctor.codegeneracy T.μ 1 0 ≫
        IteratedEndofunctor.codegeneracy T.μ 0 0 =
      IteratedEndofunctor.codegeneracy T.μ 1 1 ≫
        IteratedEndofunctor.codegeneracy T.μ 0 0 := sorry

/-- The canonical cosimplicial resolution of a monad. -/
@[stacks 0G5N "canonical cosimplicial resolution of a monad"]
noncomputable def cosimplicialResolution : CosimplicialObject (C ⥤ C) :=
  EndofunctorResolution.cosimplicial.resolution T.η T.μ
    (cosimplicialResolution.left_unit T) (cosimplicialResolution.right_unit T)
    (cosimplicialResolution.assoc T)

/-- The degree-`n` term of the canonical monad resolution is its positive `(n + 1)`-fold
iterate. -/
@[simp, stacks 0G5N "canonical monad resolution object formula"]
theorem cosimplicialResolution.obj (Δ : SimplexCategory) :
    T.cosimplicialResolution.obj Δ = T.toFunctor ⁺⦋Δ.len⦌ := sorry

/-- The canonical monad resolution evaluates a simplex morphism by its generator code. -/
@[simp, stacks 0G5N "canonical monad resolution map formula"]
theorem cosimplicialResolution.map {Δ Δ' : SimplexCategory} (θ : Δ ⟶ Δ') :
    T.cosimplicialResolution.map θ =
      EndofunctorResolution.cosimplicial.map T.η T.μ θ := sorry

/-- Cofaces in the canonical monad resolution insert the unit. -/
@[simp, stacks 0G5N "canonical monad resolution coface formula"]
theorem cosimplicialResolution.δ {n : ℕ} (i : Fin (n + 2)) :
    T.cosimplicialResolution.δ i =
      IteratedEndofunctor.coface T.η n i := sorry

/-- Codegeneracies in the canonical monad resolution apply the multiplication. -/
@[simp, stacks 0G5N "canonical monad resolution codegeneracy formula"]
theorem cosimplicialResolution.σ {n : ℕ} (i : Fin (n + 1)) :
    T.cosimplicialResolution.σ i =
      IteratedEndofunctor.codegeneracy T.μ n i := sorry

/-- The raw degreewise component induced between the resolutions of two monads. -/
@[stacks 0G5N "component of the monad resolution map"]
noncomputable def cosimplicialResolution.homApp {T S : Monad C} (alpha : T ⟶ S)
    (Δ : SimplexCategory) :
    T.toFunctor ⁺⦋Δ.len⦌ ⟶ S.toFunctor ⁺⦋Δ.len⦌ :=
  Endofunctor.iterate.map alpha.toNatTrans (Δ.len + 1)

/-- The raw components of a monad resolution map form a natural family. -/
@[stacks 0G5N "naturality of the monad resolution map"]
theorem cosimplicialResolution.homApp.naturality {T S : Monad C} (alpha : T ⟶ S)
    {Δ Δ' : SimplexCategory} (θ : Δ ⟶ Δ') :
    T.cosimplicialResolution.map θ ≫ cosimplicialResolution.homApp alpha Δ' =
      cosimplicialResolution.homApp alpha Δ ≫ S.cosimplicialResolution.map θ := sorry

/-- The cosimplicial resolution map induced by a morphism of monads. -/
@[stacks 0G5N "map of monad cosimplicial resolutions"]
noncomputable def cosimplicialResolution.hom {T S : Monad C} (alpha : T ⟶ S) :
    T.cosimplicialResolution ⟶ S.cosimplicialResolution where
  app := cosimplicialResolution.homApp alpha
  naturality := fun _ _ θ ↦ cosimplicialResolution.homApp.naturality alpha θ

/-- A monad-resolution map is degreewise the iterated underlying natural transformation. -/
@[simp, stacks 0G5N "component formula for the monad resolution map"]
theorem cosimplicialResolution.hom_app {T S : Monad C} (alpha : T ⟶ S)
    (Δ : SimplexCategory) :
    (cosimplicialResolution.hom alpha).app Δ =
      cosimplicialResolution.homApp alpha Δ := sorry

/-- The identity monad morphism induces the identity resolution map. -/
@[simp]
theorem cosimplicialResolution.hom.id (T : Monad C) :
    cosimplicialResolution.hom (𝟙 T) = 𝟙 T.cosimplicialResolution := sorry

/-- Monad resolution maps preserve composition. -/
@[simp]
theorem cosimplicialResolution.hom.comp {T S R : Monad C}
    (alpha : T ⟶ S) (beta : S ⟶ R) :
    cosimplicialResolution.hom (alpha ≫ beta) =
      cosimplicialResolution.hom alpha ≫ cosimplicialResolution.hom beta := sorry

/-- The canonical cosimplicial resolution as a functor of the monad. -/
@[stacks 0G5N "functorial monad cosimplicial resolution"]
noncomputable def cosimplicialResolution.functor :
    Monad C ⥤ CosimplicialObject (C ⥤ C) where
  obj T := T.cosimplicialResolution
  map alpha := cosimplicialResolution.hom alpha
  map_id := cosimplicialResolution.hom.id
  map_comp := cosimplicialResolution.hom.comp

/-- The canonical monad resolution realizes the positive iterates, unit cofaces, and
multiplication codegeneracies. -/
@[stacks 0G5N "canonical monad resolution realization"]
theorem cosimplicialResolution.realization : T.Realizes T.cosimplicialResolution := sorry

variable {T : Monad C}

/-- Every realization of a monad's iterated formulas is its canonical cosimplicial resolution. -/
@[stacks 0G5N "identification with the canonical monad resolution"]
theorem Realizes.eq_cosimplicialResolution {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U) : U = T.cosimplicialResolution := sorry

/-- The degree isomorphisms of a realization are natural with respect to the canonical
cosimplicial resolution. -/
@[stacks 0G5N "naturality of the canonical cosimplicial realization isomorphism"]
theorem Realizes.iso_hom_naturality {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U) {Δ Δ' : SimplexCategory} (θ : Δ ⟶ Δ') :
    U.map θ ≫ (hU.objIso Δ'.len).hom =
      (hU.objIso Δ.len).hom ≫ T.cosimplicialResolution.map θ := sorry

/-- A realization is canonically isomorphic to the monad's cosimplicial resolution. Its
components are the explicit degree isomorphisms stored by the realization witness. -/
@[stacks 0G5N "canonical isomorphism from a realization to the monad resolution"]
noncomputable def Realizes.iso {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U) : U ≅ T.cosimplicialResolution :=
  NatIso.ofComponents (fun Δ ↦ hU.objIso Δ.len)
    (fun θ ↦ Realizes.iso_hom_naturality hU θ)

/-- The forward component of the canonical realization isomorphism is the realization's
explicit degree transport. -/
@[simp, stacks 0G5N "forward component of the canonical cosimplicial realization isomorphism"]
theorem Realizes.iso_hom_app {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U) (Δ : SimplexCategory) :
    (Realizes.iso hU).hom.app Δ = (hU.objIso Δ.len).hom := sorry

/-- The inverse component of the canonical realization isomorphism is the reverse degree
transport supplied by the realization witness. -/
@[simp, stacks 0G5N "inverse component of the canonical cosimplicial realization isomorphism"]
theorem Realizes.iso_inv_app {U : CosimplicialObject (C ⥤ C)}
    (hU : T.Realizes U) (Δ : SimplexCategory) :
    (Realizes.iso hU).inv.app Δ = (hU.objIso Δ.len).inv := sorry

variable (T : Monad C)

/-- The canonical cosimplicial resolution is the unique realization of a monad's formulas. -/
@[stacks 0G5N "uniqueness of the canonical monad resolution"]
theorem Realizes.existsUnique :
    ∃! U : CosimplicialObject (C ⥤ C), T.Realizes U := sorry

end Monad

namespace EndofunctorResolution.toMonad

/-- The canonical cosimplicial resolution of the monad generated by raw unit and
multiplication data is the raw iterated-endofunctor resolution. -/
@[stacks 0G5N "raw cosimplicial resolution agrees with the generated monad resolution"]
theorem cosimplicialResolution_eq {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0) :
    (EndofunctorResolution.toMonad d s hδσ₀ hδσ₁ hσσ).cosimplicialResolution =
      EndofunctorResolution.cosimplicial.resolution d s hδσ₀ hδσ₁ hσσ := sorry

end EndofunctorResolution.toMonad

end CategoryTheory
