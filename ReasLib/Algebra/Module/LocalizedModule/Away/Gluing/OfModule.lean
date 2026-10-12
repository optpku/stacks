/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.BaseChange
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Hom
public import ReasLib.Algebra.Module.LocalizedModule.Away.Iterated.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Principal-Open Gluing Attached to a Global Module

A module over a ring restricts to every member of a principal-open family.
The two restrictions to a pairwise overlap are normalized to the same direct
product localization, which supplies the canonical overlap isomorphism.

@stack 00EK
@stack 05EL
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

noncomputable section

namespace LocalizedModule.Away

variable {R : Type u} [CommRing R]
variable {ι : Type w}

namespace PreGluing

/-- The local module on `D(f i)` obtained by localizing a global module `M`.
The universe is normalized to `max u v`, matching `ModuleCat.of` over the
localization ring. -/
@[stacks 00EK "global module principal-open local piece",
  stacks 05EL "global module principal-open local piece"]
noncomputable def ofModuleLocalModule (f : ι → R)
    (M : ModuleCat.{max u v} R) (i : ι) :
    ModuleCat.{max u v} (Localization.Away (f i)) :=
  ModuleCat.of (Localization.Away (f i))
    (LocalizedModule.Away (f i) M)

/-- The base-ring module obtained by restricting scalars on the bundled local
piece of a global module. -/
@[stacks 00EK "global module local piece restricted scalar view"]
noncomputable abbrev ofModuleLocalModuleRestrict (f : ι → R)
    (M : ModuleCat.{max u v} R) (i : ι) : ModuleCat.{max u v} R :=
  ModuleCat.of R (ofModuleLocalModule f M i)

/-- The direct canonical base-ring module on the localized carrier of a
global module. -/
@[stacks 00EK "global module local piece direct scalar view"]
noncomputable abbrev ofModuleLocalModuleDirect (f : ι → R)
    (M : ModuleCat.{max u v} R) (i : ι) : ModuleCat.{max u v} R :=
  ModuleCat.of R (LocalizedModule.Away (f i) M)

/-- Restricting scalars on the bundled local piece gives the same module as
the direct localization construction. -/
@[stacks 00EK "global module local piece scalar-action compatibility"]
theorem ofModuleLocalModuleRestrict_eq_direct (f : ι → R)
    (M : ModuleCat.{max u v} R) (i : ι) :
    ofModuleLocalModuleRestrict f M i =
      ofModuleLocalModuleDirect f M i := sorry

/-- The canonical base-ring-linear comparison between the restricted and
direct scalar views of a localized global module. -/
@[stacks 00EK "global module local piece scalar comparison"]
noncomputable def ofModuleLocalModuleEquiv (f : ι → R)
    (M : ModuleCat.{max u v} R) (i : ι) :
    ofModuleLocalModuleRestrict f M i ≃ₗ[R]
      ofModuleLocalModuleDirect f M i :=
  (eqToIso (ofModuleLocalModuleRestrict_eq_direct f M i)).toLinearEquiv

/-- The overlap module obtained by localizing the `i`-th local piece of a
global module away from a further denominator `d`. -/
@[stacks 00EK "global module principal-open overlap module"]
noncomputable def ofModuleOverlapModule (f : ι → R)
    (M : ModuleCat.{max u v} R) (i : ι) (d : R) :
    ModuleCat.{max u v} (Localization.Away d) :=
  ModuleCat.of (Localization.Away d)
    (LocalizedModule.Away d (ofModuleLocalModule f M i))

/-- Normalize the `i`-side overlap of a global module to its direct
localization away from `f i * f j`. -/
@[stacks 00EK "global module left principal-overlap normalization"]
noncomputable def ofModuleLeftOverlapIso (f : ι → R)
    (M : ModuleCat.{max u v} R) (i j : ι) :
    ofModuleOverlapModule f M i (f i * f j) ≅
      ModuleCat.of (Localization.Away (f i * f j))
        (LocalizedModule.Away (f i * f j) M) :=
  (LocalizedModule.mapEquiv (Submonoid.powers (f i * f j))
      (ofModuleLocalModuleEquiv f M i)).toModuleIso ≪≫
    (LocalizedModule.Away.Iterated.leftOverlapEquiv
      (f i) (f j) M).toModuleIso

/-- Normalize the `j`-side overlap of a global module to the same direct
localization away from `f i * f j`. -/
@[stacks 00EK "global module right principal-overlap normalization"]
noncomputable def ofModuleRightOverlapIso (f : ι → R)
    (M : ModuleCat.{max u v} R) (i j : ι) :
    ofModuleOverlapModule f M j (f i * f j) ≅
      ModuleCat.of (Localization.Away (f i * f j))
        (LocalizedModule.Away (f i * f j) M) :=
  (LocalizedModule.mapEquiv (Submonoid.powers (f i * f j))
      (ofModuleLocalModuleEquiv f M j)).toModuleIso ≪≫
    (LocalizedModule.Away.Iterated.rightOverlapEquiv
      (f i) (f j) M).toModuleIso

/-- The canonical pairwise overlap isomorphism for the localizations of a
single global module. -/
@[stacks 00EK "global module principal-open overlap isomorphism"]
noncomputable def ofModuleOverlapIso (f : ι → R)
    (M : ModuleCat.{max u v} R) (i j : ι) :
    ofModuleOverlapModule f M i (f i * f j) ≅
      ofModuleOverlapModule f M j (f i * f j) :=
  ofModuleLeftOverlapIso f M i j ≪≫
    (ofModuleRightOverlapIso f M i j).symm

/-- The principal-open pregluing datum obtained from one global module.
Its overlap maps are explicit composites through the common direct product
localization. -/
@[stacks 00EK "global module principal-open pregluing"]
noncomputable def ofModule (f : ι → R)
    (M : ModuleCat.{max u v} R) : PreGluing f where
  localModule i := ofModuleLocalModule f M i
  overlapIso i j := ofModuleOverlapIso f M i j

/-- The local piece of the pregluing attached to a global module is its
principal localization. -/
@[simp, stacks 00EK "global module pregluing local piece projection"]
theorem ofModule_localModule (f : ι → R)
    (M : ModuleCat.{max u v} R) (i : ι) :
    (ofModule f M).localModule i = ofModuleLocalModule f M i := sorry

/-- The overlap of the pregluing attached to a global module is the canonical
left-to-right normalization composite. -/
@[simp, stacks 00EK "global module pregluing overlap projection"]
theorem ofModule_overlapIso (f : ι → R)
    (M : ModuleCat.{max u v} R) (i j : ι) :
    (ofModule f M).overlapIso i j = ofModuleOverlapIso f M i j := sorry

end PreGluing

namespace Gluing

/-- The canonical overlap maps of a global module satisfy the triple-overlap
cocycle condition. -/
@[stacks 00EK "global module principal-open gluing cocycle"]
theorem ofModule_cocycle (f : ι → R) (M : ModuleCat.{max u v} R) :
    PreGluing.CocycleCondition (PreGluing.ofModule f M) := sorry

/-- The principal-open gluing datum canonically attached to a global module.
All local modules and pairwise overlap isomorphisms come from
`PreGluing.ofModule`; only the cocycle certificate is added here. -/
@[stacks 00EK "global module principal-open gluing",
  stacks 05EL "global module principal-open gluing"]
noncomputable def ofModule (f : ι → R)
    (M : ModuleCat.{max u v} R) : Gluing f where
  toPreGluing := PreGluing.ofModule f M
  cocycle := ofModule_cocycle f M

/-- Forgetting the cocycle from the gluing attached to a global module
recovers its canonical pregluing datum. -/
@[simp, stacks 00EK "global module gluing underlying pregluing"]
theorem ofModule_toPreGluing (f : ι → R)
    (M : ModuleCat.{max u v} R) :
    (ofModule f M).toPreGluing = PreGluing.ofModule f M := sorry

/-- The canonical map from a global module to its local piece on `D(f i)`.
It is expressed through the extension/restriction adjunction so that the
codomain carries exactly the scalar action of the bundled gluing field. -/
@[stacks 00EK "global module principal-open localization map",
  stacks 05EL "global module principal-open localization map"]
noncomputable def ofModuleProjection (f : ι → R)
    (M : ModuleCat.{max u v} R) (i : ι) :
    M ⟶ (ModuleCat.restrictScalars
      (algebraMap R (Localization.Away (f i)))).obj
        ((ofModule f M).localModule i) :=
  ModuleCat.ExtendRestrictScalarsAdj.Unit.map
      (algebraMap R (Localization.Away (f i))) ≫
    (ModuleCat.restrictScalars
      (algebraMap R (Localization.Away (f i)))).map
        (ModuleCat.ExtendScalars.awayIso (f i) M).hom

/-- The global-to-local projection sends `m` to its canonical localization
class on `D(f i)`. -/
@[simp, stacks 00EK "global module localization map application"]
theorem ofModuleProjection_apply (f : ι → R)
    (M : ModuleCat.{max u v} R) (i : ι) (m : M) :
    ofModuleProjection f M i m =
      LocalizedModule.mkLinearMap (Submonoid.powers (f i)) M m := sorry

/-- The family of all principal-open restrictions of a global section. -/
@[stacks 00EK "global module principal-open section family",
  stacks 05EL "global module principal-open section family"]
noncomputable def ofModuleFamilyMap (f : ι → R)
    (M : ModuleCat.{max u v} R) :
    M →ₗ[R] ((i : ι) → (ofModule f M).localModule i) :=
  LinearMap.pi fun i ↦ (ofModuleProjection f M i).hom

/-- Evaluating the family of restrictions at `i` gives the canonical
global-to-local projection on `D(f i)`. -/
@[simp, stacks 00EK "global module section family evaluation",
  stacks 05EL "global module section family evaluation"]
theorem ofModuleFamilyMap_apply (f : ι → R)
    (M : ModuleCat.{max u v} R) (m : M) (i : ι) :
    ofModuleFamilyMap f M m i = ofModuleProjection f M i m := sorry

/-- The family of principal-open restrictions of a global section satisfies
the pairwise gluing compatibility equations. -/
@[stacks 00EK "global module section family compatibility",
  stacks 05EL "global module section family compatibility"]
theorem ofModuleFamilyMap_mem (f : ι → R)
    (M : ModuleCat.{max u v} R) (m : M) :
    ofModuleFamilyMap f M m ∈ (ofModule f M).gluedModule := sorry

/-- The canonical map from a global module to the module of compatible
principal-open sections. -/
@[stacks 00EK "global module compatible principal-open section",
  stacks 05EL "global module compatible principal-open section"]
noncomputable def ofModuleSection (f : ι → R)
    (M : ModuleCat.{max u v} R) :
    M →ₗ[R] (ofModule f M).gluedModule :=
  LinearMap.codRestrict (ofModule f M).gluedModule
    (ofModuleFamilyMap f M) (ofModuleFamilyMap_mem f M)

/-- The `i`-th component of the compatible section attached to `m` is its
canonical localization on `D(f i)`. -/
@[simp, stacks 00EK "global module compatible section evaluation",
  stacks 05EL "global module compatible section evaluation"]
theorem ofModuleSection_apply (f : ι → R)
    (M : ModuleCat.{max u v} R) (m : M) (i : ι) :
    (ofModuleSection f M m).1 i = ofModuleProjection f M i m := sorry

/-- Localizing a module map at every member of a principal-open family
gives the corresponding morphism between the canonical local pieces. -/
@[stacks 00EK "global module gluing morphism local component"]
noncomputable def ofModuleMapLocal (f : ι → R)
    {M N : ModuleCat.{max u v} R} (φ : M ⟶ N) (i : ι) :
    (ofModule f M).localModule i ⟶ (ofModule f N).localModule i :=
  ModuleCat.ofHom (LocalizedModule.map (Submonoid.powers (f i)) φ.hom)

/-- Localizing a module map at every member of a principal-open family
commutes with the canonical overlap isomorphisms. -/
@[stacks 00EK "global module gluing map overlap naturality"]
theorem ofModuleMap_comm (f : ι → R)
    {M N : ModuleCat.{max u v} R} (φ : M ⟶ N) :
    ∀ i j : ι,
      CommSq
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers (f i * f j))
          ((ofModuleMapLocal f φ i).hom.restrictScalars R))
        ((ofModule f M).overlapIso i j).hom
        ((ofModule f N).overlapIso i j).hom
        (ModuleCat.ofHom <| LocalizedModule.map
          (Submonoid.powers (f i * f j))
          ((ofModuleMapLocal f φ j).hom.restrictScalars R)) := sorry

/-- A global module map induces the coordinatewise morphism between its
principal-open gluing data. -/
@[stacks 00EK "global module principal-open gluing morphism"]
noncomputable def ofModuleMap (f : ι → R)
    {M N : ModuleCat.{max u v} R} (φ : M ⟶ N) :
    ofModule f M ⟶ ofModule f N where
  hom i := ofModuleMapLocal f φ i
  comm := ofModuleMap_comm f φ

/-- The canonical global-to-local projections are natural in the global
module. -/
@[stacks 00EK "global module localization map naturality",
  stacks 05EL "global module localization map naturality"]
theorem ofModuleProjection_naturality (f : ι → R)
    {M N : ModuleCat.{max u v} R} (φ : M ⟶ N) (i : ι) :
    φ ≫ ofModuleProjection f N i =
      ofModuleProjection f M i ≫
        (ModuleCat.restrictScalars
          (algebraMap R (Localization.Away (f i)))).map
            ((ofModuleMap f φ).hom i) := sorry

/-- The compatible principal-open section map is natural in the global
module. -/
@[stacks 00EK "global module compatible section naturality",
  stacks 05EL "global module compatible section naturality"]
theorem ofModuleSection_naturality (f : ι → R)
    {M N : ModuleCat.{max u v} R} (φ : M ⟶ N) :
    (ofModuleSection f N).comp φ.hom =
      (ofModuleMap f φ).gluedMap.comp (ofModuleSection f M) := sorry

/-- The gluing morphism induced by an identity module map is the identity. -/
@[stacks 00EK "global module gluing morphism identity"]
theorem ofModuleMap_id (f : ι → R) (M : ModuleCat.{max u v} R) :
    ofModuleMap f (𝟙 M) = 𝟙 (ofModule f M) := sorry

/-- The gluing morphism induced by a composite module map is the composite
of the induced gluing morphisms. -/
@[stacks 00EK "global module gluing morphism composition"]
theorem ofModuleMap_comp (f : ι → R)
    {M N P : ModuleCat.{max u v} R} (φ : M ⟶ N) (ψ : N ⟶ P) :
    ofModuleMap f (φ ≫ ψ) = ofModuleMap f φ ≫ ofModuleMap f ψ := sorry

/-- Restriction of global modules to a principal-open family, packaged as a
functor into the category of gluing data. -/
@[stacks 00EK "global module principal-open gluing functor",
  stacks 05EL "global module principal-open gluing functor"]
noncomputable def ofModuleFunctor (f : ι → R) :
    ModuleCat.{max u v} R ⥤ Gluing f where
  obj M := ofModule f M
  map φ := ofModuleMap f φ
  map_id := ofModuleMap_id f
  map_comp := ofModuleMap_comp f

end Gluing

end LocalizedModule.Away
