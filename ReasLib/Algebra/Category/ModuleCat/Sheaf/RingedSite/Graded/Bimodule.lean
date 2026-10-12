/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module

/-!
# Graded bimodule sheaves

This leaf owns graded bimodules between algebra sheaves graded by a small additive monoid on an
arbitrary ringed site, including their category and forgetful functors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddMonoid ι]

open scoped SheafOfModules.RingedSite.GradedModuleSheaf

/-- Definition 24.8.1 (1): a graded `(A, B)`-bimodule sheaf is a right graded `B`-module
sheaf equipped with a restriction-compatible left graded `A`-action satisfying the left unit,
left associativity, and mixed associativity laws. -/
@[stacks 0FR5]
structure GradedBimodule
    (𝒪 : Sheaf J CommRingCat.{max u v})
    (A B : GradedAlgebraSheaf 𝒪 ι) where
  /-- The underlying right graded `B`-module. -/
  toRightModule : GradedModuleSheaf B
  /-- The left graded `A`-action on local sections. -/
  leftMul :
    ∀ n m (U : Cᵒᵖ),
      A.sections U n →ₗ[𝒪.obj.obj U]
        toRightModule.sections U m →ₗ[𝒪.obj.obj U] toRightModule.sections U (n + m)
  /-- The left action commutes with restriction. -/
  map_leftMul :
    ∀ {n m : ι} {U V : Cᵒᵖ} (f : U ⟶ V)
      (a : A.sections U n) (x : toRightModule.sections U m),
      (((toRightModule (n + m)).val.map f).hom) (leftMul n m U a x) =
        leftMul n m V (((A n).val.map f).hom a) (((toRightModule m).val.map f).hom x)
  /-- The left action is associative with multiplication on `A`. -/
  left_assoc :
    ∀ i j k (U : Cᵒᵖ)
      (a : A.sections U i) (a' : A.sections U j) (x : toRightModule.sections U k),
      HEq (leftMul (i + j) k U (A.mul U i j a a') x)
        (leftMul i (j + k) U a (leftMul j k U a' x))
  /-- The unit of `A` in degree zero acts trivially on the left. -/
  one_left :
    ∀ n (U : Cᵒᵖ) (x : toRightModule.sections U n),
      HEq (leftMul 0 n U (A.one U) x) x
  /-- The left `A`-action commutes with the right `B`-action. -/
  middle_assoc :
    ∀ i j k (U : Cᵒᵖ)
      (a : A.sections U i) (x : toRightModule.sections U j) (b : B.sections U k),
      HEq (toRightModule.smul (i + j) k U (leftMul i j U a x) b)
        (leftMul i (j + k) U a (toRightModule.smul j k U x b))

namespace GradedBimodule

/-- Scoped notation for graded `(A, B)`-bimodule sheaves. -/
scoped[SheafOfModules.RingedSite.GradedBimodule] notation:max "Mod(" A ", " B ")" =>
  _root_.SheafOfModules.RingedSite.GradedBimodule _ A B

end GradedBimodule

open scoped SheafOfModules.RingedSite.GradedBimodule

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "GModO" => GradedObject ι ModO

namespace GradedBimodule

/-- The underlying graded object of a graded bimodule sheaf. -/
abbrev toGradedObject
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) :
    GModO :=
  M.toRightModule.toGradedObject

/-- A graded bimodule sheaf coerces to its underlying graded object. -/
instance instCoeOutGradedObject
    (A B : GradedAlgebraSheaf 𝒪 ι) :
    CoeOut (Mod(A, B)) GModO where
  coe M := M.toGradedObject

/-- A graded bimodule sheaf evaluates to its degreewise module-sheaf family. -/
instance instCoeFun
    (A B : GradedAlgebraSheaf 𝒪 ι) :
    CoeFun (Mod(A, B)) (fun _ ↦ ι → ModO) where
  coe M := M.toGradedObject

/-- The degree-`n` term of the underlying graded object is the degree-`n` module sheaf. -/
@[simp]
theorem toGradedObject_apply
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) (n : ι) :
    M.toGradedObject n = M n := sorry

/-- Coercion of a graded bimodule sheaf recovers its degree-`n` right-module component. -/
@[simp]
theorem coe_apply
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) (n : ι) :
    M n = M.toRightModule n := sorry

/-- The degree-`n` local sections of a graded bimodule sheaf. -/
abbrev sections
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B))
    (U : Cᵒᵖ) (n : ι) : Type (max u v) :=
  M.toRightModule.sections U n

/-- Associativity of the left action as an equality after the degree-index transport. -/
theorem left_assoc_cast
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) (i j k : ι) (U : Cᵒᵖ)
    (a : A.sections U i) (a' : A.sections U j) (x : M.sections U k) :
    cast (congrArg (M.sections U) (add_assoc i j k))
      (M.leftMul (i + j) k U (A.mul U i j a a') x) =
        M.leftMul i (j + k) U a (M.leftMul j k U a' x) := sorry

/-- The left degree-zero unit action as an equality after the degree-index transport. -/
theorem one_left_cast
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) (n : ι) (U : Cᵒᵖ) (x : M.sections U n) :
    cast (congrArg (M.sections U) (zero_add n))
      (M.leftMul 0 n U (A.one U) x) = x := sorry

/-- Compatibility of the left and right actions as an equality after the degree-index transport. -/
theorem middle_assoc_cast
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) (i j k : ι) (U : Cᵒᵖ)
    (a : A.sections U i) (x : M.sections U j) (b : B.sections U k) :
    cast (congrArg (M.sections U) (add_assoc i j k))
      (M.toRightModule.smul (i + j) k U (M.leftMul i j U a x) b) =
        M.leftMul i (j + k) U a (M.toRightModule.smul j k U x b) := sorry

/-- Definition 24.8.1 (2): a homomorphism of graded bimodule sheaves is a homomorphism of the
underlying right graded modules that also commutes with the left action. -/
@[stacks 0FR5]
structure Hom
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M N : Mod(A, B)) where
  /-- The underlying homomorphism of right graded modules. -/
  toRightHom : M.toRightModule ⟶ N.toRightModule
  /-- Compatibility with the left graded action. -/
  left_comm :
    ∀ n m (U : Cᵒᵖ) (a : A.sections U n) (x : M.sections U m),
      (((toRightHom.hom (n + m)).val.app U).hom) (M.leftMul n m U a x) =
        N.leftMul n m U a ((((toRightHom.hom m).val.app U).hom) x)

namespace Hom

/-- The identity homomorphism of a graded bimodule sheaf. -/
def id
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) : Hom M M where
  toRightHom := 𝟙 M.toRightModule
  left_comm := sorry

/-- The composite of graded bimodule sheaf homomorphisms. -/
def comp
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N P : Mod(A, B)}
    (f : Hom M N) (g : Hom N P) : Hom M P where
  toRightHom := f.toRightHom ≫ g.toRightHom
  left_comm := sorry

/-- The underlying right-module map of the identity bimodule map is the identity. -/
@[simp]
theorem id_toRightHom
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) :
    (id M).toRightHom = 𝟙 M.toRightModule := sorry

/-- The underlying right-module map of a composite is the composite of right-module maps. -/
@[simp]
theorem comp_toRightHom
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N P : Mod(A, B)}
    (f : Hom M N) (g : Hom N P) :
    (comp f g).toRightHom = f.toRightHom ≫ g.toRightHom := sorry

end Hom

/-- A graded bimodule homomorphism coerces to its underlying right graded-module map. -/
instance instCoeOutHom
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N : Mod(A, B)} :
    CoeOut (Hom M N) (M.toRightModule ⟶ N.toRightModule) where
  coe f := f.toRightHom

/-- A graded bimodule homomorphism evaluates degreewise. -/
instance instCoeFunHom
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M N : Mod(A, B)) :
    CoeFun (Hom M N) (fun _ ↦ ∀ n : ι, M n ⟶ N n) where
  coe f := f.toRightHom.hom

/-- Coercion of a bimodule homomorphism recovers its degree-`n` component. -/
@[simp]
theorem hom_coe_apply
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N : Mod(A, B)}
    (f : Hom M N) (n : ι) :
    f n = f.toRightHom.hom n := sorry

/-- The degree-`n` component of the identity bimodule map is the identity. -/
@[simp]
theorem id_hom
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) (n : ι) :
    Hom.id M n = 𝟙 (M n) := sorry

/-- The degree-`n` component of a composite bimodule map is the composite of components. -/
@[simp]
theorem comp_hom
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N P : Mod(A, B)}
    (f : Hom M N) (g : Hom N P) (n : ι) :
    Hom.comp f g n = f n ≫ g n := sorry

/-- Two graded bimodule homomorphisms are equal when their degreewise components agree. -/
@[ext]
theorem hom_ext
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N : Mod(A, B)} (f g : Hom M N)
    (h : ∀ n : ι, f n = g n) : f = g := sorry

/-- The underlying right graded-module map determines a graded bimodule homomorphism. -/
theorem toRightHom_injective
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N : Mod(A, B)} :
    Function.Injective (fun f : Hom M N ↦ f.toRightHom) := sorry

/-- Identity and composition make graded bimodule sheaves into a category. -/
@[stacks 0FR5]
instance instCategory
    (A B : GradedAlgebraSheaf 𝒪 ι) :
    Category (Mod(A, B)) where
  Hom M N := Hom M N
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The forgetful functor from graded bimodule sheaves to their right graded-module sheaves. -/
def forgetToRightModule
    (A B : GradedAlgebraSheaf 𝒪 ι) :
    Mod(A, B) ⥤ Mod(B) where
  obj M := M.toRightModule
  map f := f.toRightHom
  map_id := sorry
  map_comp := sorry

/-- The right-module forgetful functor preserves identities. -/
@[simp]
theorem forgetToRightModule_map_id
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) :
    (forgetToRightModule A B).map (𝟙 M) = 𝟙 M.toRightModule := sorry

/-- The right-module forgetful functor preserves composition. -/
@[simp]
theorem forgetToRightModule_map_comp
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N P : Mod(A, B)}
    (f : M ⟶ N) (g : N ⟶ P) :
    (forgetToRightModule A B).map (f ≫ g) =
      (forgetToRightModule A B).map f ≫ (forgetToRightModule A B).map g := sorry

/-- Forgetting a graded bimodule sheaf recovers its stored right graded-module datum. -/
@[simp]
theorem forgetToRightModule_obj
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) :
    (forgetToRightModule A B).obj M = M.toRightModule := sorry

/-- Forgetting a graded bimodule map recovers its underlying right graded-module map. -/
@[simp]
theorem forgetToRightModule_map
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N : Mod(A, B)}
    (f : M ⟶ N) :
    (forgetToRightModule A B).map f = f.toRightHom := sorry

/-- Forgetting to the underlying right graded module is faithful. -/
instance forgetToRightModule_faithful
    (A B : GradedAlgebraSheaf 𝒪 ι) :
    Functor.Faithful (forgetToRightModule A B) where
  map_injective := sorry

/-- The forgetful functor from graded bimodule sheaves to their underlying graded module sheaves. -/
abbrev forgetToGraded
    (A B : GradedAlgebraSheaf 𝒪 ι) :
    Mod(A, B) ⥤ GModO :=
  forgetToRightModule A B ⋙ GradedModuleSheaf.forgetToGraded B

/-- The graded-object forgetful functor preserves identities. -/
@[simp]
theorem forgetToGraded_map_id
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) :
    (forgetToGraded A B).map (𝟙 M) = 𝟙 M.toGradedObject := sorry

/-- The graded-object forgetful functor preserves composition. -/
@[simp]
theorem forgetToGraded_map_comp
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N P : Mod(A, B)}
    (f : M ⟶ N) (g : N ⟶ P) :
    (forgetToGraded A B).map (f ≫ g) =
      (forgetToGraded A B).map f ≫ (forgetToGraded A B).map g := sorry

/-- The bimodule-to-graded-object forgetful functor factors through the right-module forgetful
functor. -/
theorem forgetToGraded_def
    (A B : GradedAlgebraSheaf 𝒪 ι) :
    forgetToGraded A B =
      forgetToRightModule A B ⋙ GradedModuleSheaf.forgetToGraded B := sorry

/-- Forgetting a graded bimodule sheaf to graded objects recovers its underlying graded object. -/
@[simp]
theorem forgetToGraded_obj
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) :
    (forgetToGraded A B).obj M = M.toGradedObject := sorry

/-- Forgetting a graded bimodule map to graded objects recovers its graded-object map. -/
@[simp]
theorem forgetToGraded_map
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N : Mod(A, B)} (f : M ⟶ N) :
    (forgetToGraded A B).map f = f.toRightHom.hom := sorry

/-- The forgotten graded object evaluates to the original degree-`n` module sheaf. -/
@[simp]
theorem forgetToGraded_obj_apply
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) (n : ι) :
    ((forgetToGraded A B).obj M) n = M n := sorry

/-- The forgotten graded-object map evaluates to the original degree-`n` component. -/
@[simp]
theorem forgetToGraded_map_apply
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N : Mod(A, B)} (f : M ⟶ N) (n : ι) :
    ((forgetToGraded A B).map f) n = f.toRightHom.hom n := sorry

/-- Forgetting to the underlying graded object is faithful. -/
instance forgetToGraded_faithful
    (A B : GradedAlgebraSheaf 𝒪 ι) :
    Functor.Faithful (forgetToGraded A B) where
  map_injective := sorry

end GradedBimodule

end

end SheafOfModules.RingedSite
