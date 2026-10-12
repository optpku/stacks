/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.OfModule.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# The Canonical Formal-Gluing Functor

A source module determines a formal gluing object: extend it to the target
ring, localize it over the source principal-open family, and use the canonical
base-change comparison between the resulting target-side gluing data.

@stack 05EL
-/

@[expose] public section

open CategoryTheory

universe u v w

noncomputable section

namespace LocalizedModule.Away.FormalGluing

variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι : Type w}

/-- The formal gluing object canonically attached to a source module. -/
@[stacks 05EL "canonical formal gluing of a module"]
noncomputable def ofModule (φ : R →+* S) (f : ι → R)
    (M : ModuleCat.{max u v} R) : FormalGluing φ f where
  globalModule := (ModuleCat.extendScalars φ).obj M
  sourceGluing := Gluing.ofModule f M
  comparisonIso := Gluing.ofModuleBaseChangeIso φ f M

/-- The extended global map and localized source map of a module morphism
form a commuting formal-gluing comparison square. -/
@[stacks 05EL "canonical formal gluing morphism comparison square"]
theorem ofModuleMap_comm (φ : R →+* S) (f : ι → R)
    {M N : ModuleCat.{max u v} R} (ψ : M ⟶ N) :
    CommSq
      (Gluing.ofModuleMap (fun i ↦ φ (f i))
        ((ModuleCat.extendScalars φ).map ψ))
      (Gluing.ofModuleBaseChangeIso φ f M).hom
      (Gluing.ofModuleBaseChangeIso φ f N).hom
      (Gluing.baseChangeMap φ (Gluing.ofModuleMap f ψ)) := sorry

/-- A source module morphism induces a morphism between its canonical formal
gluing objects. -/
@[stacks 05EL "canonical formal gluing morphism"]
noncomputable def ofModuleMap (φ : R →+* S) (f : ι → R)
    {M N : ModuleCat.{max u v} R} (ψ : M ⟶ N) :
    ofModule φ f M ⟶ ofModule φ f N where
  globalMap := (ModuleCat.extendScalars φ).map ψ
  sourceMap := Gluing.ofModuleMap f ψ
  comm := ofModuleMap_comm φ f ψ

/-- The canonical formal-gluing construction sends an identity module map
to the identity morphism. -/
@[stacks 05EL "canonical formal gluing identity"]
theorem ofModuleMap_id (φ : R →+* S) (f : ι → R)
    (M : ModuleCat.{max u v} R) :
    ofModuleMap φ f (𝟙 M) = 𝟙 (ofModule φ f M) := sorry

/-- The canonical formal-gluing construction preserves composition of
module maps. -/
@[stacks 05EL "canonical formal gluing composition"]
theorem ofModuleMap_comp (φ : R →+* S) (f : ι → R)
    {M N P : ModuleCat.{max u v} R} (ψ : M ⟶ N) (χ : N ⟶ P) :
    ofModuleMap φ f (ψ ≫ χ) =
      ofModuleMap φ f ψ ≫ ofModuleMap φ f χ := sorry

/-- The canonical functor from source modules to formal gluing objects. -/
@[stacks 05EL "canonical formal gluing functor"]
noncomputable def ofModuleFunctor (φ : R →+* S) (f : ι → R) :
    ModuleCat.{max u v} R ⥤ FormalGluing φ f where
  obj M := ofModule φ f M
  map ψ := ofModuleMap φ f ψ
  map_id := ofModuleMap_id φ f
  map_comp := ofModuleMap_comp φ f

end LocalizedModule.Away.FormalGluing
