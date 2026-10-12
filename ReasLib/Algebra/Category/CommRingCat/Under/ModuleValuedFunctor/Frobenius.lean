/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.RightExact
public import ReasLib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace ModuleValuedFunctor.Frobenius

variable (p : ℕ) [Fact p.Prime]

/-- The prime `p` vanishes in every commutative algebra over `ZMod p`. -/
theorem primeCast_eq_zero (B : Under (CommRingCat.of (ZMod p))) :
    (p : B.right) = 0 := sorry

/-- The Frobenius endomorphism of a commutative `ZMod p`-algebra. -/
def ringHom (B : Under (CommRingCat.of (ZMod p))) : B.right →+* B.right :=
  RingHom.frobeniusOfPrime p (primeCast_eq_zero p B)

/-- The Frobenius endomorphism sends `b` to `b ^ p`. -/
theorem ringHom_apply (B : Under (CommRingCat.of (ZMod p))) (b : B.right) :
    ringHom p B b = b ^ p := sorry

/-- A morphism of `ZMod p`-algebras is additive on the Frobenius-twisted regular modules. -/
theorem transition_add {B B' : Under (CommRingCat.of (ZMod p))} (f : B ⟶ B')
    (x y : B.right) :
    f.right.hom (x + y) = f.right.hom x + f.right.hom y := sorry

/-- A morphism of `ZMod p`-algebras is linear between the Frobenius-twisted regular modules. -/
theorem transition_smul {B B' : Under (CommRingCat.of (ZMod p))} (f : B ⟶ B')
    (b x : B.right) :
    f.right.hom (ringHom p B b * x) =
      ringHom p B' (f.right.hom b) * f.right.hom x := sorry

/-- The additive transition map intertwines the two bundled scalar actions. -/
theorem transition_smul_naturality {B B' : Under (CommRingCat.of (ZMod p))}
    (f : B ⟶ B') (b : B.right) :
    AddCommGrpCat.ofHom (RingHom.toAddMonoidHom f.right.hom) ≫
        ((ModuleCat.restrictScalars f.right.hom).obj
          ((ModuleCat.restrictScalars (ringHom p B')).obj
            (ModuleCat.of B'.right B'.right))).smul b =
      ((ModuleCat.restrictScalars (ringHom p B)).obj
          (ModuleCat.of B.right B.right)).smul b ≫
        AddCommGrpCat.ofHom (RingHom.toAddMonoidHom f.right.hom) := sorry

/-- The transition map between Frobenius-twisted regular modules. -/
noncomputable def transition {B B' : Under (CommRingCat.of (ZMod p))} (f : B ⟶ B') :
    (ModuleCat.restrictScalars (ringHom p B)).obj (ModuleCat.of B.right B.right) ⟶
      (ModuleCat.restrictScalars f.right.hom).obj
        ((ModuleCat.restrictScalars (ringHom p B')).obj (ModuleCat.of B'.right B'.right)) :=
  ModuleCat.homMk (AddCommGrpCat.ofHom (RingHom.toAddMonoidHom f.right.hom))
    (transition_smul_naturality p f)

/-- The transition map has underlying function `f.right.hom`. -/
theorem transition_apply {B B' : Under (CommRingCat.of (ZMod p))} (f : B ⟶ B')
    (x : B.right) :
    transition p f x = f.right.hom x := sorry

/-- Frobenius transition along an identity is the identity on elements. -/
theorem transition_id (B : Under (CommRingCat.of (ZMod p))) (x : B.right) :
    transition p (𝟙 B) x = x := sorry

/-- Frobenius transitions respect composition. -/
theorem transition_comp {B B' B'' : Under (CommRingCat.of (ZMod p))}
    (f : B ⟶ B') (g : B' ⟶ B'') (x : B.right) :
    transition p (f ≫ g) x = transition p g (transition p f x) := sorry

/-- The module-valued functor whose value on `B` is its regular module with scalar
action `b • x = b ^ p * x`. -/
noncomputable def functor : ModuleValuedFunctor (CommRingCat.of (ZMod p)) where
  obj B := (ModuleCat.restrictScalars (ringHom p B)).obj (ModuleCat.of B.right B.right)
  map f := transition p f
  map_id B := transition_id p B
  map_comp f g := transition_comp p f g

/-- Scalar multiplication in the value of the Frobenius functor is the twisted action. -/
theorem obj_smul (B : Under (CommRingCat.of (ZMod p))) (b : B.right)
    (x : (functor p).obj B) :
    b • x = ((ModuleCat.of B.right B.right).smul (b ^ p)).hom x := sorry

/-- The Frobenius functor sends a morphism to its underlying ring homomorphism. -/
theorem map_apply {B B' : Under (CommRingCat.of (ZMod p))} (f : B ⟶ B')
    (x : (functor p).obj B) :
    (functor p).map f x = f.right.hom x := sorry

/-- Reading the square-zero coordinate from a tangent vector is additive. -/
theorem tangentHom_add (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (x y : (functor p).tangentObj B N) :
    ((functor p).tangentι B N (x + y)).2 =
      ((functor p).tangentι B N x).2 + ((functor p).tangentι B N y).2 := sorry

/-- Reading the square-zero coordinate from the zero tangent vector gives zero. -/
theorem tangentHom_zero (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right) :
    ((functor p).tangentι B N 0).2 = 0 := sorry

/-- The additive map underlying the Frobenius-twisted tangent-coordinate map. -/
noncomputable def tangentAddHom (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    (forget₂ (ModuleCat B.right) AddCommGrpCat).obj ((functor p).tangentObj B N) ⟶
      (forget₂ (ModuleCat B.right) AddCommGrpCat).obj
        ((ModuleCat.restrictScalars (ringHom p B)).obj N) :=
  AddCommGrpCat.ofHom {
    toFun := fun x ↦ ((functor p).tangentι B N x).2
    map_zero' := tangentHom_zero p B N
    map_add' := tangentHom_add p B N }

/-- The underlying additive tangent-coordinate map reads the square-zero coordinate. -/
theorem tangentAddHom_apply (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) (x : (functor p).tangentObj B N) :
    tangentAddHom p B N x = ((functor p).tangentι B N x).2 := sorry

/-- The additive tangent-coordinate map intertwines the two bundled scalar actions. -/
theorem tangentAddHom_smul_naturality (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) (b : B.right) :
    tangentAddHom p B N ≫
        ((ModuleCat.restrictScalars (ringHom p B)).obj N).smul b =
      ((functor p).tangentObj B N).smul b ≫ tangentAddHom p B N := sorry

/-- The tangent coordinate map into `N` with its Frobenius-restricted scalar action. -/
noncomputable def tangentHom (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    (functor p).tangentObj B N ⟶ (ModuleCat.restrictScalars (ringHom p B)).obj N :=
  ModuleCat.homMk (tangentAddHom p B N) (tangentAddHom_smul_naturality p B N)

/-- The tangent coordinate map reads the second square-zero coordinate. -/
theorem tangentHom_apply (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (x : (functor p).tangentObj B N) :
    tangentHom p B N x = ((functor p).tangentι B N x).2 := sorry

/-- The pure square-zero element `TrivSqZeroExt.inr n` lies in the tangent kernel. -/
theorem tangentInv_mem (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (n : N) :
    TrivSqZeroExt.inr n ∈ ((functor p).tangentAugmentation B N).hom.ker := sorry

/-- The tangent vector represented by the pure square-zero element `TrivSqZeroExt.inr n`. -/
noncomputable def tangentInvValue (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) (n : N) : (functor p).tangentObj B N :=
  ⟨TrivSqZeroExt.inr n, tangentInv_mem p B N n⟩

/-- The kernel inclusion sends `tangentInvValue n` to `TrivSqZeroExt.inr n`. -/
theorem tangentInvValue_ι (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (n : N) :
    (functor p).tangentι B N (tangentInvValue p B N n) = TrivSqZeroExt.inr n := sorry

/-- Pure square-zero tangent vectors preserve addition. -/
theorem tangentInv_add (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (x y : N) :
    tangentInvValue p B N (x + y) =
      tangentInvValue p B N x + tangentInvValue p B N y := sorry

/-- Pure square-zero insertion sends zero to the zero tangent vector. -/
theorem tangentInv_zero (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right) :
    tangentInvValue p B N 0 = 0 := sorry

/-- The additive map underlying insertion of pure square-zero tangent vectors. -/
noncomputable def tangentInvAddHom (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    (forget₂ (ModuleCat B.right) AddCommGrpCat).obj
        ((ModuleCat.restrictScalars (ringHom p B)).obj N) ⟶
      (forget₂ (ModuleCat B.right) AddCommGrpCat).obj ((functor p).tangentObj B N) :=
  AddCommGrpCat.ofHom {
    toFun := tangentInvValue p B N
    map_zero' := tangentInv_zero p B N
    map_add' := tangentInv_add p B N }

/-- The underlying additive insertion map sends `n` to its pure square-zero vector. -/
theorem tangentInvAddHom_apply (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) (n : N) :
    tangentInvAddHom p B N n = tangentInvValue p B N n := sorry

/-- The additive pure square-zero insertion intertwines the bundled scalar actions. -/
theorem tangentInvAddHom_smul_naturality (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) (b : B.right) :
    tangentInvAddHom p B N ≫ ((functor p).tangentObj B N).smul b =
      ((ModuleCat.restrictScalars (ringHom p B)).obj N).smul b ≫
        tangentInvAddHom p B N := sorry

/-- The inverse tangent-coordinate map, induced by `TrivSqZeroExt.inr`. -/
noncomputable def tangentInv (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    (ModuleCat.restrictScalars (ringHom p B)).obj N ⟶ (functor p).tangentObj B N :=
  ModuleCat.homMk (tangentInvAddHom p B N) (tangentInvAddHom_smul_naturality p B N)

/-- The inverse tangent-coordinate map sends `n` to its pure square-zero tangent vector. -/
theorem tangentInv_apply (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (n : N) :
    tangentInv p B N n = tangentInvValue p B N n := sorry

/-- The tangent-coordinate map followed by its inverse is the identity. -/
theorem tangentHom_comp_tangentInv (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    tangentHom p B N ≫ tangentInv p B N = 𝟙 _ := sorry

/-- The inverse tangent-coordinate map followed by the coordinate map is the identity. -/
theorem tangentInv_comp_tangentHom (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    tangentInv p B N ≫ tangentHom p B N = 𝟙 _ := sorry

/-- The componentwise identification of the tangent module with Frobenius restriction. -/
noncomputable def tangentIsoApp (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    (functor p).tangentObj B N ≅ (ModuleCat.restrictScalars (ringHom p B)).obj N where
  hom := tangentHom p B N
  inv := tangentInv p B N
  hom_inv_id := tangentHom_comp_tangentInv p B N
  inv_hom_id := tangentInv_comp_tangentHom p B N

/-- The hom of `tangentIsoApp` is the tangent-coordinate map. -/
theorem tangentIsoApp_hom (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    (tangentIsoApp p B N).hom = tangentHom p B N := sorry

/-- The tangent components commute with maps of modules. -/
theorem tangentIso_naturality (B : Under (CommRingCat.of (ZMod p)))
    {N N' : ModuleCat B.right} (f : N ⟶ N') :
    ((functor p).tangent.fixedBase B).map f ≫ (tangentIsoApp p B N').hom =
      (tangentIsoApp p B N).hom ≫ (ModuleCat.restrictScalars (ringHom p B)).map f := sorry

/-- The fixed-base tangent functor is naturally isomorphic to restriction of scalars
along Frobenius. -/
noncomputable def tangentIso (B : Under (CommRingCat.of (ZMod p))) :
    (functor p).tangent.fixedBase B ≅ ModuleCat.restrictScalars (ringHom p B) :=
  CategoryTheory.NatIso.ofComponents (tangentIsoApp p B) (tangentIso_naturality p B)

/-- The hom component of `tangentIso` reads the second square-zero coordinate. -/
theorem tangentIso_hom_app (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (x : (functor p).tangentObj B N) :
    (tangentIso p B).hom.app N x = ((functor p).tangentι B N x).2 := sorry

/-- The inverse component of `tangentIso` inserts a pure square-zero element. -/
theorem tangentIso_inv_app (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (n : N) :
    (tangentIso p B).inv.app N n = tangentInvValue p B N n := sorry

/-- The Frobenius tangent functor is right exact at every base algebra. -/
theorem tangentRightExact (B : Under (CommRingCat.of (ZMod p))) :
    rightExactFunctor (ModuleCat B.right) (ModuleCat B.right)
      ((functor p).tangent.fixedBase B) := sorry

/-- The canonical carrier identification from the argument-induced tangent object. -/
noncomputable def argumentToTangent (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right)
    (x : ((functor p).tangentArgument (tangentRightExact p) B).obj N) :
    (functor p).tangentObj B N :=
  Eq.mp ((functor p).tangentArgument_obj (tangentRightExact p) B N) x

/-- The canonical carrier identification into the argument-induced tangent object. -/
noncomputable def tangentToArgument (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) (x : (functor p).tangentObj B N) :
    ((functor p).tangentArgument (tangentRightExact p) B).obj N :=
  Eq.mpr ((functor p).tangentArgument_obj (tangentRightExact p) B N) x

/-- The two canonical carrier identifications are inverse in the tangent direction. -/
theorem argumentToTangent_tangentToArgument (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) (x : (functor p).tangentObj B N) :
    argumentToTangent p B N (tangentToArgument p B N x) = x := sorry

/-- The two canonical carrier identifications are inverse in the argument direction. -/
theorem tangentToArgument_argumentToTangent (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right)
    (x : ((functor p).tangentArgument (tangentRightExact p) B).obj N) :
    tangentToArgument p B N (argumentToTangent p B N x) = x := sorry

/-- The coordinate map is additive on the argument-induced tangent module. -/
theorem argumentHom_add (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (x y : ((functor p).tangentArgument (tangentRightExact p) B).obj N) :
    tangentHom p B N (argumentToTangent p B N (x + y)) =
      tangentHom p B N (argumentToTangent p B N x) +
        tangentHom p B N (argumentToTangent p B N y) := sorry

/-- The coordinate map is linear from the argument-induced action to the ordinary action. -/
theorem argumentHom_smul (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (b : B.right) (x : ((functor p).tangentArgument (tangentRightExact p) B).obj N) :
    (tangentHom p B N (argumentToTangent p B N (b • x)) : N) =
      (N.smul b).hom (tangentHom p B N (argumentToTangent p B N x) : N) := sorry

/-- The coordinate map from the argument-induced tangent module to the ordinary module. -/
noncomputable def argumentHom (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    ((functor p).tangentArgument (tangentRightExact p) B).obj N ⟶ N :=
  ModuleCat.ofHom ({
    toFun := fun x ↦ (tangentHom p B N (argumentToTangent p B N x) : N)
    map_add' := argumentHom_add p B N
    map_smul' := argumentHom_smul p B N } :
      ((functor p).tangentArgument (tangentRightExact p) B).obj N →ₗ[B.right] N)

/-- The argument-coordinate map has the same underlying function as `tangentHom`. -/
theorem argumentHom_apply (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (x : ((functor p).tangentArgument (tangentRightExact p) B).obj N) :
    argumentHom p B N x = tangentHom p B N (argumentToTangent p B N x) := sorry

/-- Pure square-zero insertion is additive for the ordinary and argument-induced actions. -/
theorem argumentInv_add (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (x y : N) :
    tangentToArgument p B N (tangentInvValue p B N (x + y)) =
      tangentToArgument p B N (tangentInvValue p B N x) +
        tangentToArgument p B N (tangentInvValue p B N y) := sorry

/-- Pure square-zero insertion is linear for the ordinary and argument-induced actions. -/
theorem argumentInv_smul (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (b : B.right) (x : N) :
    tangentToArgument p B N (tangentInvValue p B N (b • x)) =
      b • tangentToArgument p B N (tangentInvValue p B N x) := sorry

/-- The inverse coordinate map from the ordinary module to the argument-induced tangent module. -/
noncomputable def argumentInv (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    N ⟶ ((functor p).tangentArgument (tangentRightExact p) B).obj N :=
  ModuleCat.ofHom ({
    toFun := fun n ↦ tangentToArgument p B N (tangentInvValue p B N n)
    map_add' := argumentInv_add p B N
    map_smul' := argumentInv_smul p B N } :
      N →ₗ[B.right] ((functor p).tangentArgument (tangentRightExact p) B).obj N)

/-- The inverse argument-coordinate map inserts a pure square-zero tangent vector. -/
theorem argumentInv_apply (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
    (n : N) :
    argumentInv p B N n = tangentToArgument p B N (tangentInvValue p B N n) := sorry

/-- The argument-coordinate map followed by its inverse is the identity. -/
theorem argumentHom_comp_argumentInv (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    argumentHom p B N ≫ argumentInv p B N = 𝟙 _ := sorry

/-- The inverse argument-coordinate map followed by the coordinate map is the identity. -/
theorem argumentInv_comp_argumentHom (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    argumentInv p B N ≫ argumentHom p B N = 𝟙 _ := sorry

/-- The componentwise identification of the argument-induced action with the ordinary one. -/
noncomputable def argumentIsoApp (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    ((functor p).tangentArgument (tangentRightExact p) B).obj N ≅ N where
  hom := argumentHom p B N
  inv := argumentInv p B N
  hom_inv_id := argumentHom_comp_argumentInv p B N
  inv_hom_id := argumentInv_comp_argumentHom p B N

/-- The hom of `argumentIsoApp` is the ordinary tangent-coordinate map. -/
theorem argumentIsoApp_hom (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    (argumentIsoApp p B N).hom = argumentHom p B N := sorry

/-- The argument-action components commute with maps of modules. -/
theorem argumentIso_naturality (B : Under (CommRingCat.of (ZMod p)))
    {N N' : ModuleCat B.right} (f : N ⟶ N') :
    ((functor p).tangentArgument (tangentRightExact p) B).map f ≫
        (argumentIsoApp p B N').hom =
      (argumentIsoApp p B N).hom ≫ (𝟭 (ModuleCat B.right)).map f := sorry

/-- The scalar action induced by functoriality in the module argument is naturally
isomorphic to the ordinary `B`-module structure. -/
noncomputable def argumentIso (B : Under (CommRingCat.of (ZMod p))) :
    (functor p).tangentArgument (tangentRightExact p) B ≅ 𝟭 (ModuleCat B.right) :=
  CategoryTheory.NatIso.ofComponents (argumentIsoApp p B) (argumentIso_naturality p B)

/-- The hom component of `argumentIso` is the ordinary tangent-coordinate map. -/
theorem argumentIso_hom_app (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right)
    (x : ((functor p).tangentArgument (tangentRightExact p) B).obj N) :
    (argumentIso p B).hom.app N x =
      tangentHom p B N (argumentToTangent p B N x) := sorry

/-- The inverse component of `argumentIso` inserts a pure square-zero element. -/
theorem argumentIso_inv_app (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) (n : N) :
    (argumentIso p B).inv.app N n =
      tangentToArgument p B N (tangentInvValue p B N n) := sorry

/-- The Frobenius-twisted and ordinary module actions need not agree for commutative
`ZMod p`-algebras and their modules. -/
theorem actionsDiffer :
    ∃ (B : Under (CommRingCat.of (ZMod p))) (N : ModuleCat B.right)
      (b : B.right) (n : N), ringHom p B b • n ≠ b • n := sorry

/-- A pure square-zero element has zero `p`-th power. -/
theorem squareZeroInr_pow (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) (n : N) :
    (TrivSqZeroExt.inr n : TrivSqZeroExt B.right N) ^ p = 0 := sorry

/-- The canonical tensor-to-tangent map for the argument-induced module structure is zero. -/
theorem tensorComparison_eq_zero (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    (functor p).tensorToTangentArgument (tangentRightExact p) B N = 0 := sorry

/-- The kernel-valued tensor comparison is also zero. -/
theorem tensorToTangent_eq_zero (B : Under (CommRingCat.of (ZMod p)))
    (N : ModuleCat B.right) :
    (functor p).tensorToTangentApp B N = 0 := sorry

end ModuleValuedFunctor.Frobenius
