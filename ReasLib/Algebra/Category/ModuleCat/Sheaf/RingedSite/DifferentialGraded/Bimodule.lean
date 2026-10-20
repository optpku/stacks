/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module

/-!
# Differential graded bimodule sheaves

This leaf owns differential graded bimodules between differential graded algebra sheaves on an
arbitrary ringed site, including their category and forgetful functors.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- A differential graded `(𝒜, 𝒝)`-bimodule sheaf is a right
differential graded `𝒝`-module sheaf with a compatible left `𝒜`-action satisfying
associativity, unit, commutation, and Leibniz compatibilities. -/
@[stacks 0FRQ]
structure DifferentialGradedBimodule (𝒜 𝒝 : DGA(𝒪)) where
  /-- The underlying right differential graded `𝒝`-module. -/
  toRightModule : Mod(𝒝, d)
  /-- The degreewise left action. -/
  leftMul (n m : ℤ) :
    𝒜.toComplex.X n ⊗ toRightModule.toComplex.X m ⟶ toRightModule.toComplex.X (n + m)
  /-- Compatibility of the left action with multiplication on `𝒜`. -/
  left_assoc :
    ∀ i j k : ℤ,
      (α_ (𝒜.toComplex.X i) (𝒜.toComplex.X j) (toRightModule.toComplex.X k)).hom ≫
          (𝒜.toComplex.X i ◁ leftMul j k) ≫
          leftMul i (j + k) =
        (𝒜.mul i j ▷ toRightModule.toComplex.X k) ≫
          leftMul (i + j) k ≫
          eqToHom (congrArg toRightModule.toComplex.X (Int.add_assoc i j k))
  /-- Commutation of the left `𝒜`-action with the right `𝒝`-action. -/
  middle_assoc :
    ∀ i j k : ℤ,
      (α_ (𝒜.toComplex.X i) (toRightModule.toComplex.X j) (𝒝.toComplex.X k)).hom ≫
          (𝒜.toComplex.X i ◁ toRightModule.smul j k) ≫
          leftMul i (j + k) =
        (leftMul i j ▷ 𝒝.toComplex.X k) ≫
          toRightModule.smul (i + j) k ≫
          eqToHom (congrArg toRightModule.toComplex.X (Int.add_assoc i j k))
  /-- The unit of `𝒜` acts by the identity on the left. -/
  one_left :
    ∀ n : ℤ,
      (λ_ (toRightModule.toComplex.X n)).hom =
        (𝒜.one ▷ toRightModule.toComplex.X n) ≫
          leftMul 0 n ≫
          eqToHom (congrArg toRightModule.toComplex.X (zero_add n))
  /-- Compatibility of the differential with the left action. -/
  d_leftMul :
    ∀ n m : ℤ,
      leftMul n m ≫ toRightModule.toComplex.d (n + m) (n + m + 1) =
        ((𝒜.toComplex.d n (n + 1)) ▷ toRightModule.toComplex.X m) ≫
          leftMul (n + 1) m ≫
          eqToHom
            (congrArg toRightModule.toComplex.X
              ((Int.add_assoc n 1 m).trans
                ((congrArg (fun p : ℤ ↦ n + p) (Int.add_comm 1 m)).trans
                  (Int.add_assoc n m 1).symm))) +
        n.negOnePow •
          ((𝒜.toComplex.X n ◁ toRightModule.toComplex.d m (m + 1)) ≫
            leftMul n (m + 1) ≫
            eqToHom
              (congrArg toRightModule.toComplex.X
                (Int.add_assoc n m 1).symm))

namespace DifferentialGradedBimodule

/-- Scoped notation for differential graded bimodule sheaves. -/
scoped[SheafOfModules.RingedSite.DifferentialGradedBimodule] notation:max
    "Mod(" 𝒜:arg ", " 𝒝:arg ", " "d" ")" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedBimodule 𝒜 𝒝

end DifferentialGradedBimodule

open scoped SheafOfModules.RingedSite.DifferentialGradedBimodule

namespace DifferentialGradedBimodule

/-- A differential graded bimodule sheaf coerces to its underlying right module sheaf. -/
instance instCoeOutRightModule (𝒜 𝒝 : DGA(𝒪)) :
    CoeOut (Mod(𝒜, 𝒝, d)) (Mod(𝒝, d)) where
  coe M := M.toRightModule

/-- The underlying cochain complex of a differential graded bimodule sheaf. -/
@[reducible]
def toComplex {𝒜 𝒝 : DGA(𝒪)} (M : DifferentialGradedBimodule 𝒜 𝒝) :
    CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ :=
  M.toRightModule.toComplex

/-- A differential graded bimodule sheaf coerces to its underlying cochain complex. -/
instance instCoeOutComplex (𝒜 𝒝 : DGA(𝒪)) :
    CoeOut (Mod(𝒜, 𝒝, d)) (CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ) where
  coe M := M.toComplex

/-- A differential graded bimodule sheaf evaluates degreewise on its underlying cochain complex. -/
instance instCoeFun (𝒜 𝒝 : DGA(𝒪)) :
    CoeFun (Mod(𝒜, 𝒝, d)) (fun _ ↦ ℤ → ringedSiteModuleCategory J 𝒪) where
  coe M := M.toComplex.X

/-- The underlying cochain complex evaluates to the degree-`n` component of the bimodule sheaf. -/
@[simp]
theorem toComplex_X {𝒜 𝒝 : DGA(𝒪)} (M : Mod(𝒜, 𝒝, d)) (n : ℤ) :
    M.toComplex.X n = M n := sorry

/-- Coercion of a differential graded bimodule sheaf recovers its degree-`n` component. -/
@[simp]
theorem coe_apply {𝒜 𝒝 : DGA(𝒪)} (M : Mod(𝒜, 𝒝, d)) (n : ℤ) :
    M n = M.toComplex.X n := sorry

/-- A homomorphism of differential graded `(𝒜, 𝒝)`-bimodule
sheaves is a homomorphism of right differential graded `𝒝`-modules compatible with the left
`𝒜`-action. -/
@[stacks 0FRQ, ext]
structure Hom {𝒜 𝒝 : DGA(𝒪)} (M N : Mod(𝒜, 𝒝, d)) where
  /-- The underlying homomorphism of right differential graded `𝒝`-modules. -/
  toRightHom : DifferentialGradedModule.Hom M.toRightModule N.toRightModule
  /-- Compatibility with the left action. -/
  comm_leftMul :
    ∀ n m : ℤ,
      M.leftMul n m ≫ toRightHom (n + m) =
        (𝒜.toComplex.X n ◁ toRightHom m) ≫ N.leftMul n m

namespace Hom

/-- The identity homomorphism of a differential graded bimodule sheaf. -/
def id {𝒜 𝒝 : DGA(𝒪)} (M : Mod(𝒜, 𝒝, d)) : Hom M M where
  toRightHom := DifferentialGradedModule.Hom.id M.toRightModule
  comm_leftMul := sorry

/-- The composite of differential graded bimodule homomorphisms. -/
def comp {𝒜 𝒝 : DGA(𝒪)} {M N P : Mod(𝒜, 𝒝, d)}
    (f : Hom M N) (g : Hom N P) : Hom M P where
  toRightHom := DifferentialGradedModule.Hom.comp f.toRightHom g.toRightHom
  comm_leftMul := sorry

/-- The underlying right-module map of the identity bimodule homomorphism is the identity. -/
@[simp]
theorem id_toRightHom {𝒜 𝒝 : DGA(𝒪)} (M : Mod(𝒜, 𝒝, d)) :
    (id M).toRightHom = DifferentialGradedModule.Hom.id M.toRightModule := sorry

/-- The underlying right-module map of a composite is the composite of right-module maps. -/
@[simp]
theorem comp_toRightHom {𝒜 𝒝 : DGA(𝒪)} {M N P : Mod(𝒜, 𝒝, d)}
    (f : Hom M N) (g : Hom N P) :
    (comp f g).toRightHom = DifferentialGradedModule.Hom.comp f.toRightHom g.toRightHom := sorry

/-- Composing the identity bimodule homomorphism on the left leaves a homomorphism unchanged. -/
theorem id_comp {𝒜 𝒝 : DGA(𝒪)} {M N : Mod(𝒜, 𝒝, d)} (f : Hom M N) :
    comp (id M) f = f := sorry

/-- Composing the identity bimodule homomorphism on the right leaves a homomorphism unchanged. -/
theorem comp_id {𝒜 𝒝 : DGA(𝒪)} {M N : Mod(𝒜, 𝒝, d)} (f : Hom M N) :
    comp f (id N) = f := sorry

/-- Composition of differential graded bimodule homomorphisms is associative. -/
theorem assoc {𝒜 𝒝 : DGA(𝒪)} {M N P Q : Mod(𝒜, 𝒝, d)}
    (f : Hom M N) (g : Hom N P) (h : Hom P Q) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom

/-- A differential graded bimodule homomorphism coerces to its underlying right-module map. -/
instance instCoeOutHom {𝒜 𝒝 : DGA(𝒪)} {M N : Mod(𝒜, 𝒝, d)} :
    CoeOut (Hom M N) (DifferentialGradedModule.Hom M.toRightModule N.toRightModule) where
  coe f := f.toRightHom

/-- A differential graded bimodule homomorphism evaluates degreewise. -/
instance instCoeFunHom {𝒜 𝒝 : DGA(𝒪)} (M N : Mod(𝒜, 𝒝, d)) :
    CoeFun (Hom M N) (fun _ ↦ ∀ n : ℤ, M n ⟶ N n) where
  coe f := f.toRightHom

/-- Coercion of a differential graded bimodule homomorphism recovers its degree-`n` component. -/
@[simp]
theorem hom_coe_apply {𝒜 𝒝 : DGA(𝒪)} {M N : Mod(𝒜, 𝒝, d)} (f : Hom M N) (n : ℤ) :
    f n = f.toRightHom n := sorry

/-- Two differential graded bimodule homomorphisms are equal when their degreewise components
agree. -/
@[ext]
theorem hom_ext {𝒜 𝒝 : DGA(𝒪)} {M N : Mod(𝒜, 𝒝, d)} (f g : Hom M N)
    (h : ∀ n : ℤ, f n = g n) : f = g := sorry

/-- The underlying right-module homomorphism determines a differential graded bimodule
homomorphism. -/
theorem toRightHom_injective {𝒜 𝒝 : DGA(𝒪)} {M N : Mod(𝒜, 𝒝, d)} :
    Function.Injective
      (fun f : Hom M N ↦
        (f.toRightHom : DifferentialGradedModule.Hom M.toRightModule N.toRightModule)) := sorry

/-- The degree-`n` component of the identity bimodule homomorphism is the identity. -/
@[simp]
theorem id_hom {𝒜 𝒝 : DGA(𝒪)} (M : Mod(𝒜, 𝒝, d)) (n : ℤ) :
    Hom.id M n = 𝟙 (M n) := sorry

/-- The degree-`n` component of a composite is the composite of degree-`n` components. -/
@[simp]
theorem comp_hom {𝒜 𝒝 : DGA(𝒪)} {M N P : Mod(𝒜, 𝒝, d)}
    (f : Hom M N) (g : Hom N P) (n : ℤ) :
    Hom.comp f g n = f n ≫ g n := sorry

/-- Compatible right-module maps make differential graded bimodule sheaves into a category. -/
instance instCategory (𝒜 𝒝 : DGA(𝒪)) : Category (Mod(𝒜, 𝒝, d)) where
  Hom M N := Hom M N
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- Forget the left differential graded action of a bimodule sheaf. -/
def forgetToRightModule (𝒜 𝒝 : DGA(𝒪)) : Mod(𝒜, 𝒝, d) ⥤ Mod(𝒝, d) where
  obj M := M.toRightModule
  map f := f.toRightHom
  map_id M := Hom.id_toRightHom M
  map_comp f g := Hom.comp_toRightHom f g

/-- Forgetting a bimodule sheaf to right modules recovers its stored right module sheaf. -/
@[simp]
theorem forgetToRightModule_obj {𝒜 𝒝 : DGA(𝒪)} (M : Mod(𝒜, 𝒝, d)) :
    (forgetToRightModule 𝒜 𝒝).obj M = M.toRightModule := sorry

/-- Forgetting a bimodule map to right modules recovers its underlying right-module map. -/
@[simp]
theorem forgetToRightModule_map {𝒜 𝒝 : DGA(𝒪)} {M N : Mod(𝒜, 𝒝, d)} (f : M ⟶ N) :
    (forgetToRightModule 𝒜 𝒝).map f = f.toRightHom := sorry

/-- Forgetting to the underlying right differential graded module is faithful. -/
instance forgetToRightModule_faithful (𝒜 𝒝 : DGA(𝒪)) :
    Functor.Faithful (forgetToRightModule 𝒜 𝒝) where
  map_injective := sorry

/-- Forget all bimodule structure while retaining the underlying cochain complex. -/
abbrev forgetToComplex (𝒜 𝒝 : DGA(𝒪)) :
    Mod(𝒜, 𝒝, d) ⥤ CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ :=
  forgetToRightModule 𝒜 𝒝 ⋙ DifferentialGradedModule.forgetToComplex 𝒝

/-- The bimodule-to-complex forgetful functor factors through the right-module forgetful functor. -/
theorem forgetToComplex_def (𝒜 𝒝 : DGA(𝒪)) :
    forgetToComplex 𝒜 𝒝 =
      forgetToRightModule 𝒜 𝒝 ⋙ DifferentialGradedModule.forgetToComplex 𝒝 := sorry

/-- Forgetting a bimodule sheaf to cochain complexes recovers its underlying cochain complex. -/
@[simp]
theorem forgetToComplex_obj {𝒜 𝒝 : DGA(𝒪)} (M : Mod(𝒜, 𝒝, d)) :
    (forgetToComplex 𝒜 𝒝).obj M = M.toComplex := sorry

/-- Forgetting a bimodule map to cochain complexes recovers its underlying cochain map. -/
@[simp]
theorem forgetToComplex_map {𝒜 𝒝 : DGA(𝒪)} {M N : Mod(𝒜, 𝒝, d)} (f : M ⟶ N) :
    (forgetToComplex 𝒜 𝒝).map f = f.toRightHom.toCochainMap := sorry

/-- The degree-`n` component of a forgotten bimodule map is its original degree-`n` component. -/
@[simp]
theorem forgetToComplex_map_f {𝒜 𝒝 : DGA(𝒪)} {M N : Mod(𝒜, 𝒝, d)}
    (f : M ⟶ N) (n : ℤ) :
    ((forgetToComplex 𝒜 𝒝).map f).f n = f.toRightHom n := sorry

/-- Forgetting to cochain complexes is faithful. -/
instance forgetToComplex_faithful (𝒜 𝒝 : DGA(𝒪)) :
    Functor.Faithful (forgetToComplex 𝒜 𝒝) where
  map_injective := sorry

end DifferentialGradedBimodule

end

end SheafOfModules.RingedSite
