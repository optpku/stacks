/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change on sections of a module presheaf

For a commutative-ring presheaf `O`, an arrow `f : X ⟶ Y`, and an `O`-module presheaf
`M`, restriction is semilinear along `O.map f`.  Its adjoint transpose is the canonical map

`M(X) ⊗[O(X)] O(Y) ⟶ M(Y)`.

This construction is independent of a topology or sheaf condition.  The identity and
composition comparison isomorphisms below make its pseudofunctorial source explicit.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Presheaf

noncomputable section

universe u v w z

namespace PresheafOfModules.BaseChange

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- Evaluation at `X`, retaining the commutative coefficient-ring view needed by extension of
scalars. -/
abbrev evaluation (X : Cᵒᵖ) :
    PresheafOfModules.{max w z} (ringPresheafOfComm O) ⥤
      ModuleCat.{max w z} (O.obj X) :=
  PresheafOfModules.evaluation (ringPresheafOfComm O) X

/-- Evaluate at `X` and extend scalars along `O.map f : O(X) ⟶ O(Y)`. -/
abbrev functor {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    PresheafOfModules.{max w z} (ringPresheafOfComm O) ⥤
      ModuleCat.{max w z} (O.obj Y) :=
  evaluation O X ⋙
    ModuleCat.extendScalars.{w, w, max w z} ((O.map f).hom)

/-- The adjoint transpose of restriction, `M(X) ⊗[O(X)] O(Y) ⟶ M(Y)`. -/
@[stacks 0GZN "presheaf base-change map"]
noncomputable def map
    (M : PresheafOfModules.{max w z} (ringPresheafOfComm O))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (functor O f).obj M ⟶ (evaluation O Y).obj M :=
  ((ModuleCat.extendRestrictScalarsAdj.{max w z, w, w}
    ((O.map f).hom)).homEquiv _ _).symm (M.map f)

/-- The base-change map is the adjoint transpose of the restriction map. -/
theorem map_def
    (M : PresheafOfModules.{max w z} (ringPresheafOfComm O))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    map O M f =
      ((ModuleCat.extendRestrictScalarsAdj.{max w z, w, w}
        ((O.map f).hom)).homEquiv _ _).symm (M.map f) := sorry

/-- Base change on sections is natural in the module presheaf. -/
theorem map_naturality
    {M N : PresheafOfModules.{max w z} (ringPresheafOfComm O)} (a : M ⟶ N)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (functor O f).map a ≫ map O N f =
      map O M f ≫ (evaluation O Y).map a := sorry

/-- The natural base-change comparison associated to `f`. -/
@[stacks 0GZN "natural presheaf base-change comparison"]
noncomputable def natTrans {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    functor O f ⟶ evaluation O Y where
  app M := map O M f
  naturality _ _ a := map_naturality O a f

/-- The component of `natTrans O f` is the base-change map. -/
theorem natTrans_app
    (M : PresheafOfModules.{max w z} (ringPresheafOfComm O))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (natTrans O f).app M = map O M f := sorry

/-- The canonical identification of base change along an identity with evaluation. -/
noncomputable def idSourceIso
    (M : PresheafOfModules.{max w z} (ringPresheafOfComm O)) (X : Cᵒᵖ) :
    (functor O (𝟙 X)).obj M ≅ (evaluation O X).obj M :=
  eqToIso (congrArg
      (fun h : (O.obj X : Type w) →+* (O.obj X : Type w) ↦
        (ModuleCat.extendScalars.{w, w, max w z} h).obj (M.obj X))
      (congrArg CommRingCat.Hom.hom (O.map_id X))) ≪≫
    (ModuleCat.extendScalarsId.{w, max w z} (O.obj X)).app (M.obj X)

/-- Base change sends an identity restriction to the canonical identity comparison. -/
theorem map_id
    (M : PresheafOfModules.{max w z} (ringPresheafOfComm O)) (X : Cᵒᵖ) :
    map O M (𝟙 X) = (idSourceIso O M X).hom := sorry

/-- The canonical identification of base change along a composite with iterated base change. -/
noncomputable def compSourceIso
    (M : PresheafOfModules.{max w z} (ringPresheafOfComm O))
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (functor O (f ≫ g)).obj M ≅
      (ModuleCat.extendScalars.{w, w, max w z} ((O.map g).hom)).obj
        ((functor O f).obj M) :=
  eqToIso (congrArg
      (fun h : (O.obj X : Type w) →+* (O.obj Z : Type w) ↦
        (ModuleCat.extendScalars.{w, w, max w z} h).obj (M.obj X))
      (congrArg CommRingCat.Hom.hom (O.map_comp f g))) ≪≫
    (ModuleCat.extendScalarsComp.{w, max w z}
      ((O.map f).hom) ((O.map g).hom)).app (M.obj X)

/-- Base change along a composite is the composite of the two base-change maps after the
canonical source identification. -/
theorem map_comp
    (M : PresheafOfModules.{max w z} (ringPresheafOfComm O))
    {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map O M (f ≫ g) =
      (compSourceIso O M f g).hom ≫
        (ModuleCat.extendScalars.{w, w, max w z} ((O.map g).hom)).map (map O M f) ≫
          map O M g := sorry

/-- Compatibility with base change along one specified restriction map. -/
def compatibleAt {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ObjectProperty (PresheafOfModules.{max w z} (ringPresheafOfComm O)) :=
  fun M ↦ IsIso (map O M f)

/-- Module presheaves for which every canonical base-change map is an isomorphism. -/
@[stacks 0GZN "presheaf base-change compatibility"]
def compatible :
    ObjectProperty (PresheafOfModules.{max w z} (ringPresheafOfComm O)) :=
  fun M ↦ ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y), compatibleAt O f M

/-- Base-change compatibility is the pointwise isomorphism condition on the canonical maps. -/
theorem compatible_iff
    (M : PresheafOfModules.{max w z} (ringPresheafOfComm O)) :
    compatible O M ↔
      ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y), IsIso (map O M f) := sorry

end PresheafOfModules.BaseChange
