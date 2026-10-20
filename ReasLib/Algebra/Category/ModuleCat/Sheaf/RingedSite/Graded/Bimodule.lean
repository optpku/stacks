module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module

/-!
# Graded bimodule sheaves

Graded bimodule sheaves over algebra sheaves on a ringed site have compatible left and right
actions graded by an additive monoid. Their degree-preserving homomorphisms have explicit
identity and composition operations and an unregistered category datum.
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

/-- A graded `(A, B)`-bimodule sheaf is a right graded `B`-module
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
      (((toRightModule.obj (n + m)).val.map f).hom) (leftMul n m U a x) =
        leftMul n m V (((A.obj n).val.map f).hom a) (((toRightModule.obj m).val.map f).hom x)
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

namespace GradedBimodule

/-- The underlying graded object of a graded bimodule sheaf. -/
def toGradedObject
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) :
    GradedObject ι (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) :=
  M.toRightModule.obj

/-- The degree-`n` term of the underlying graded object is the degree-`n` module sheaf. -/
@[simp]
theorem toGradedObject_apply
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) (n : ι) :
    M.toGradedObject n = M.toRightModule.obj n := sorry

/-- The degree-`n` local sections of a graded bimodule sheaf. -/
abbrev sections
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B))
    (U : Cᵒᵖ) (n : ι) : Type (max u v) :=
  (M.toRightModule.obj n).val.obj U

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

/-- A homomorphism of graded bimodule sheaves is a homomorphism of the
underlying right graded modules that also commutes with the left action. -/
@[stacks 0FR5]
structure Hom
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M N : Mod(A, B)) where
  /-- The underlying homomorphism of right graded modules. -/
  toRightHom : GradedModuleSheaf.Hom M.toRightModule N.toRightModule
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
  toRightHom := GradedModuleSheaf.Hom.id M.toRightModule
  left_comm := sorry

/-- The composite of graded bimodule sheaf homomorphisms. -/
def comp
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N P : Mod(A, B)}
    (f : Hom M N) (g : Hom N P) : Hom M P where
  toRightHom := GradedModuleSheaf.Hom.comp f.toRightHom g.toRightHom
  left_comm := sorry

/-- The underlying right-module map of the identity bimodule map is the identity. -/
@[simp]
theorem id_toRightHom
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) :
    (id M).toRightHom = GradedModuleSheaf.Hom.id M.toRightModule := sorry

/-- The underlying right-module map of a composite is the composite of right-module maps. -/
@[simp]
theorem comp_toRightHom
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N P : Mod(A, B)}
    (f : Hom M N) (g : Hom N P) :
    (comp f g).toRightHom = GradedModuleSheaf.Hom.comp f.toRightHom g.toRightHom := sorry

end Hom

/-- The degree-`n` component of the identity bimodule map is the identity. -/
@[simp]
theorem id_hom
    {A B : GradedAlgebraSheaf 𝒪 ι}
    (M : Mod(A, B)) (n : ι) :
    (Hom.id M).toRightHom.hom n = 𝟙 (M.toRightModule.obj n) := sorry

/-- The degree-`n` component of a composite bimodule map is the composite of components. -/
@[simp]
theorem comp_hom
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N P : Mod(A, B)}
    (f : Hom M N) (g : Hom N P) (n : ι) :
    (Hom.comp f g).toRightHom.hom n = f.toRightHom.hom n ≫ g.toRightHom.hom n := sorry

/-- Two graded bimodule homomorphisms are equal when their degreewise components agree. -/
@[ext]
theorem hom_ext
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N : Mod(A, B)} (f g : Hom M N)
    (h : ∀ n : ι, f.toRightHom.hom n = g.toRightHom.hom n) : f = g := sorry

/-- The underlying right graded-module map determines a graded bimodule homomorphism. -/
theorem toRightHom_injective
    {A B : GradedAlgebraSheaf 𝒪 ι}
    {M N : Mod(A, B)} :
    Function.Injective (fun f : Hom M N ↦ f.toRightHom) := sorry

/-- Identity and composition make graded bimodule sheaves into a category. -/
@[reducible, stacks 0FR5]
def category
    (A B : GradedAlgebraSheaf 𝒪 ι) :
    Category (Mod(A, B)) where
  Hom M N := Hom M N
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

end GradedBimodule

end

end SheafOfModules.RingedSite
