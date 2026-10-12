/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Internal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Gluing morphisms of module sheaves

Morphisms of module sheaves form the global sections of the internal-Hom sheaf.  Consequently,
a compatible family of morphisms after restriction to objects covering the terminal object has a
unique global realization.  The public API records this as a proposition; it does not choose a
global morphism from the sheaf condition.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite (ringSheaf ringedSiteModuleCategory)

noncomputable section

universe u v w t

namespace SheafOfModules.RingedSite.InternalHom

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{max u v w})

/-- A family of morphisms between restrictions, regarded as a family of elements of the
underlying type-valued internal-Hom sheaf. -/
@[stacks 03EM "local family of module-sheaf morphisms"]
abbrev localFamily
    {F G : ringedSiteModuleCategory J O} {I : Type t} (X : I → C)
    (f : ∀ i, F.over (X i) ⟶ G.over (X i)) :
    Presheaf.FamilyOfElementsOnObjects
      (ToInternal.carrier (ringSheaf J O) (obj O F G)).obj X :=
  fun i ↦
    (ToInternal.sectionEquiv (ringSheaf J O) (obj O F G) (op (X i))).symm (f i)

/-- Compatibility of a local morphism family says precisely that its pullbacks along any two
maps to members of the cover agree. -/
@[stacks 03EM "compatibility of local module-sheaf morphisms"]
theorem localFamily_isCompatible_iff
    {F G : ringedSiteModuleCategory J O} {I : Type t} (X : I → C)
    (f : ∀ i, F.over (X i) ⟶ G.over (X i)) :
    (localFamily O X f).IsCompatible ↔
      ∀ (Z : C) (i j : I) (a : Z ⟶ X i) (b : Z ⟶ X j),
        restrictFun O F G a.op (f i) = restrictFun O F G b.op (f j) := sorry

/-- A global module-sheaf morphism realizes a local family when its restriction to each chosen
object is the prescribed morphism. -/
@[stacks 03EM "global realization of a local morphism family"]
def IsGluing
    {F G : ringedSiteModuleCategory J O} {I : Type t} (X : I → C)
    (f : ∀ i, F.over (X i) ⟶ G.over (X i)) (g : F ⟶ G) : Prop :=
  ∀ i, g.over (X i) = f i

/-- A compatible local family on objects covering the terminal object has a unique global
realization.  This is the choice-free gluing interface for module-sheaf morphisms. -/
@[stacks 03EM "existence and uniqueness of gluing module-sheaf morphisms"]
theorem existsUnique_isGluing
    {F G : ringedSiteModuleCategory J O} {I : Type t} {X : I → C}
    (hX : J.CoversTop X) (f : ∀ i, F.over (X i) ⟶ G.over (X i))
    (hf : (localFamily O X f).IsCompatible) :
    ∃! g : F ⟶ G, IsGluing O X f g := sorry

/-- Two module-sheaf morphisms are equal if their restrictions agree on objects covering the
terminal object. -/
@[stacks 03EM "cover-local extensionality for module-sheaf morphisms"]
theorem hom_ext_of_coversTop
    {F G : ringedSiteModuleCategory J O} {I : Type t} {X : I → C}
    (hX : J.CoversTop X) {f g : F ⟶ G}
    (h : ∀ i, f.over (X i) = g.over (X i)) : f = g := sorry

/-- Any two global realizations of the same local family on a cover are equal. -/
@[stacks 03EM "uniqueness of a global realization of local morphisms"]
theorem isGluing_unique
    {F G : ringedSiteModuleCategory J O} {I : Type t} {X : I → C}
    (hX : J.CoversTop X) (f : ∀ i, F.over (X i) ⟶ G.over (X i))
    {g h : F ⟶ G} (hg : IsGluing O X f g) (hh : IsGluing O X f h) :
    g = h := sorry

-- `localFamily` and `IsGluing` contain only their displayed inputs.  Existence and uniqueness
-- remain Prop-valued, so this module never extracts morphism data from a provisional sheaf proof.

end SheafOfModules.RingedSite.InternalHom
