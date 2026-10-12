/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Scheme and ringed-space presentations of module sheaves

Mathlib's `Scheme.Modules` and ReasLib's `RingedSpace.Modules` use the same sheaves of modules as
objects and the same module-sheaf morphisms as arrows.  They install distinct category instances,
however, so downstream APIs need explicit identity-on-data functors rather than relying on
definitional unfolding at every use site.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Regard a module sheaf in Mathlib's scheme presentation as the same sheaf in the ringed-space
presentation. -/
def toRingedSpaceObj (X : Scheme.{u}) (M : X.Modules) : X.toRingedSpace.Modules :=
  M

/-- Regard a morphism in Mathlib's scheme-module presentation as the same module-sheaf morphism in
the ringed-space presentation. -/
def toRingedSpaceMap (X : Scheme.{u}) {M N : X.Modules} (f : M ⟶ N) :
    toRingedSpaceObj X M ⟶ toRingedSpaceObj X N :=
  f

/-- The identity law for the identity-on-data passage to the ringed-space presentation. -/
theorem toRingedSpaceMap_id (X : Scheme.{u}) (M : X.Modules) :
    toRingedSpaceMap X (𝟙 M) = 𝟙 (toRingedSpaceObj X M) := sorry

/-- The composition law for the identity-on-data passage to the ringed-space presentation. -/
theorem toRingedSpaceMap_comp (X : Scheme.{u})
    {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) :
    toRingedSpaceMap X (f ≫ g) = toRingedSpaceMap X f ≫ toRingedSpaceMap X g := sorry

/-- The identity-on-data functor from Mathlib's scheme-module presentation to the ringed-space
module presentation. -/
def toRingedSpace (X : Scheme.{u}) : X.Modules ⥤ X.toRingedSpace.Modules where
  obj := toRingedSpaceObj X
  map := toRingedSpaceMap X
  map_id := toRingedSpaceMap_id X
  map_comp := toRingedSpaceMap_comp X

/-- The identity-on-data object map from the ringed-space module presentation back to Mathlib's
scheme-module presentation. -/
def fromRingedSpaceObj (X : Scheme.{u}) (M : X.toRingedSpace.Modules) : X.Modules :=
  M

/-- The identity-on-data morphism map from the ringed-space module presentation back to Mathlib's
scheme-module presentation. -/
def fromRingedSpaceMap (X : Scheme.{u})
    {M N : X.toRingedSpace.Modules} (f : M ⟶ N) :
    fromRingedSpaceObj X M ⟶ fromRingedSpaceObj X N :=
  f

/-- The identity law for the identity-on-data passage from the ringed-space presentation. -/
theorem fromRingedSpaceMap_id (X : Scheme.{u}) (M : X.toRingedSpace.Modules) :
    fromRingedSpaceMap X (𝟙 M) = 𝟙 (fromRingedSpaceObj X M) := sorry

/-- The composition law for the identity-on-data passage from the ringed-space presentation. -/
theorem fromRingedSpaceMap_comp (X : Scheme.{u})
    {M N P : X.toRingedSpace.Modules}
    (f : M ⟶ N) (g : N ⟶ P) :
    fromRingedSpaceMap X (f ≫ g) = fromRingedSpaceMap X f ≫ fromRingedSpaceMap X g := sorry

/-- The identity-on-data functor from the ringed-space module presentation back to Mathlib's
scheme-module presentation. -/
def fromRingedSpace (X : Scheme.{u}) : X.toRingedSpace.Modules ⥤ X.Modules where
  obj := fromRingedSpaceObj X
  map := fromRingedSpaceMap X
  map_id := fromRingedSpaceMap_id X
  map_comp := fromRingedSpaceMap_comp X

/-- The identity-on-data comparison isomorphisms satisfy the triangle identity. -/
theorem ringedSpaceEquivalence_triangle (X : Scheme.{u}) (M : X.Modules) :
    (toRingedSpace X).map (𝟙 M) ≫ 𝟙 ((toRingedSpace X).obj M) =
      𝟙 ((toRingedSpace X).obj M) := sorry

/-- The two identity-on-data functors identify Mathlib's scheme-module category with the
ringed-space module category of the underlying ringed space.  Both comparison isomorphisms are
definitionally the identity; only the triangle law is proof data. -/
@[stacks 01BE "ambient module presentation bridge"]
def ringedSpaceEquivalence (X : Scheme.{u}) : X.Modules ≌ X.toRingedSpace.Modules where
  functor := toRingedSpace X
  inverse := fromRingedSpace X
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := ringedSpaceEquivalence_triangle X

/-- The forward presentation functor does not change the underlying module sheaf. -/
@[simp]
theorem toRingedSpace_obj {X : Scheme.{u}} (M : X.Modules) :
    (toRingedSpace X).obj M = M := sorry

/-- The forward presentation functor does not change the underlying module-sheaf morphism. -/
@[simp]
theorem toRingedSpace_map {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    (toRingedSpace X).map f = f := sorry

/-- The inverse presentation functor does not change the underlying module sheaf. -/
@[simp]
theorem fromRingedSpace_obj {X : Scheme.{u}} (M : X.toRingedSpace.Modules) :
    (fromRingedSpace X).obj M = M := sorry

/-- The inverse presentation functor does not change the underlying module-sheaf morphism. -/
@[simp]
theorem fromRingedSpace_map {X : Scheme.{u}}
    {M N : X.toRingedSpace.Modules} (f : M ⟶ N) :
    (fromRingedSpace X).map f = f := sorry

end AlgebraicGeometry.Scheme.Modules
