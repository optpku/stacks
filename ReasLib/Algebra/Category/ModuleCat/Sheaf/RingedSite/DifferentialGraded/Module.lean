/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Algebra

/-!
# Differential graded module sheaves

This leaf owns right modules over a differential graded algebra sheaf on an arbitrary ringed site,
together with their category and the forgetful functor to cochain complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}

-- Local declaration justification (parser conflict): this lexical alias avoids introducing a
-- public `Mod(𝒪)` notation overlapping the established differential-graded `Mod(...)` scope; it
-- carries no local choice or instance.
local notation "ModO" => ringedSiteModuleCategory J 𝒪
-- Local declaration justification (parser conflict): this complex alias is tied to the preceding
-- ambient-module parser boundary and carries no local choice or instance.
local notation "CpxO" => CochainComplex ModO ℤ

/-- Definition 24.13.1 (1): a differential graded `𝒜`-module sheaf is a cochain complex of
`𝒪`-modules with a degreewise right `𝒜`-action satisfying associativity, the unit law, and the
Leibniz rule. -/
@[stacks 0FRI]
structure DifferentialGradedModule (𝒜 : DGA(𝒪)) where
  /-- The underlying cochain complex of `𝒪`-modules. -/
  toComplex : CpxO
  /-- The degreewise right action. -/
  smul : ∀ n m : ℤ, toComplex.X n ⊗ 𝒜.toComplex.X m ⟶ toComplex.X (n + m)
  /-- Compatibility of the action with multiplication on `𝒜`. -/
  smul_assoc :
    ∀ n m k : ℤ,
      (α_ (toComplex.X n) (𝒜.toComplex.X m) (𝒜.toComplex.X k)).hom ≫
          (toComplex.X n ◁ 𝒜.mul m k) ≫
          smul n (m + k) =
        (smul n m ▷ 𝒜.toComplex.X k) ≫
          smul (n + m) k ≫
          eqToHom (congrArg toComplex.X (Int.add_assoc n m k))
  /-- The unit of `𝒜` acts by the identity. -/
  one_smul :
    ∀ n : ℤ,
      (ρ_ (toComplex.X n)).hom =
        (toComplex.X n ◁ 𝒜.one) ≫
          smul n 0 ≫
          eqToHom (congrArg toComplex.X (add_zero n))
  /-- Compatibility of the differential with the action. -/
  d_smul :
    ∀ n m : ℤ,
      smul n m ≫ toComplex.d (n + m) (n + m + 1) =
        ((toComplex.d n (n + 1)) ▷ 𝒜.toComplex.X m) ≫
          smul (n + 1) m ≫
          eqToHom
            (congrArg toComplex.X
              ((Int.add_assoc n 1 m).trans
                ((congrArg (fun p : ℤ ↦ n + p) (Int.add_comm 1 m)).trans
                  (Int.add_assoc n m 1).symm))) +
        n.negOnePow •
          ((toComplex.X n ◁ 𝒜.toComplex.d m (m + 1)) ≫
            smul n (m + 1) ≫
            eqToHom
              (congrArg toComplex.X
                (Int.add_assoc n m 1).symm))

namespace DifferentialGradedModule

/-- Scoped notation for differential graded right module sheaves. -/
scoped[SheafOfModules.RingedSite.DifferentialGradedModule] notation:max
    "Mod(" 𝒜:arg ", " "d" ")" =>
  _root_.SheafOfModules.RingedSite.DifferentialGradedModule 𝒜

end DifferentialGradedModule

open scoped SheafOfModules.RingedSite.DifferentialGradedModule

/-- A differential graded module sheaf coerces to its underlying cochain complex. -/
instance instCoeOutDifferentialGradedModule (𝒜 : DGA(𝒪)) :
    CoeOut (Mod(𝒜, d)) CpxO where
  coe ℳ := ℳ.toComplex

namespace DifferentialGradedModule

/-- A differential graded module sheaf evaluates degreewise on its underlying cochain complex. -/
instance instCoeFun {𝒜 : DGA(𝒪)} :
    CoeFun (Mod(𝒜, d)) (fun _ ↦ ℤ → ModO) where
  coe ℳ := ℳ.toComplex.X

/-- Coercion of a differential graded module sheaf recovers its degree-`n` component. -/
@[simp]
theorem coe_apply {𝒜 : DGA(𝒪)} (ℳ : Mod(𝒜, d)) (n : ℤ) :
    ℳ n = ℳ.toComplex.X n := sorry

/-- The underlying cochain complex evaluates to the degree-`n` component of the module sheaf. -/
@[simp]
theorem toComplex_X {𝒜 : DGA(𝒪)} (ℳ : Mod(𝒜, d)) (n : ℤ) :
    ℳ.toComplex.X n = ℳ n := sorry

/-- Definition 24.13.1 (2): a homomorphism of differential graded `𝒜`-module sheaves is a
cochain map compatible with the right action. -/
@[stacks 0FRI, ext]
structure Hom {𝒜 : DGA(𝒪)} (ℳ N : Mod(𝒜, d)) where
  /-- The underlying morphism of cochain complexes. -/
  toCochainMap : ℳ.toComplex ⟶ N.toComplex
  /-- Compatibility with the right `𝒜`-action. -/
  comm :
    ∀ n m : ℤ,
      ℳ.smul n m ≫ toCochainMap.f (n + m) =
        ((toCochainMap.f n) ▷ 𝒜.toComplex.X m) ≫ N.smul n m

/-- A differential graded module homomorphism coerces to its underlying cochain map. -/
instance instCoeOutHom {𝒜 : DGA(𝒪)} (ℳ N : Mod(𝒜, d)) :
    CoeOut (Hom ℳ N) (ℳ.toComplex ⟶ N.toComplex) where
  coe f := f.toCochainMap

/-- A differential graded module homomorphism evaluates degreewise. -/
instance instCoeFunHom {𝒜 : DGA(𝒪)} {ℳ N : Mod(𝒜, d)} :
    CoeFun (Hom ℳ N) (fun _ ↦ ∀ n : ℤ, ℳ n ⟶ N n) where
  coe f := f.toCochainMap.f

/-- Coercion of a differential graded module homomorphism recovers its degree-`n` component. -/
@[simp]
theorem hom_coe_apply {𝒜 : DGA(𝒪)} {ℳ N : Mod(𝒜, d)} (f : Hom ℳ N) (n : ℤ) :
    f n = f.toCochainMap.f n := sorry

/-- The cochain-map component of a differential graded module homomorphism is its degreewise
component. -/
@[simp]
theorem toCochainMap_f {𝒜 : DGA(𝒪)} {ℳ N : Mod(𝒜, d)} (f : Hom ℳ N) (n : ℤ) :
    f.toCochainMap.f n = f n := sorry

/-- Two differential graded module homomorphisms are equal when their degreewise components
agree. -/
@[ext]
theorem hom_ext {𝒜 : DGA(𝒪)} {ℳ N : Mod(𝒜, d)} (f g : Hom ℳ N)
    (h : ∀ n : ℤ, f n = g n) : f = g := sorry

/-- The underlying cochain map determines a differential graded module homomorphism. -/
theorem toCochainMap_injective {𝒜 : DGA(𝒪)} {ℳ N : Mod(𝒜, d)} :
    Function.Injective (fun f : Hom ℳ N ↦ f.toCochainMap) := sorry

namespace Hom

/-- The identity homomorphism of a differential graded module sheaf. -/
def id {𝒜 : DGA(𝒪)} (ℳ : Mod(𝒜, d)) : Hom ℳ ℳ where
  toCochainMap := 𝟙 ℳ.toComplex
  comm := sorry

/-- The composite of differential graded module homomorphisms. -/
def comp {𝒜 : DGA(𝒪)} {ℳ N P : Mod(𝒜, d)} (f : Hom ℳ N) (g : Hom N P) : Hom ℳ P where
  toCochainMap := f.toCochainMap ≫ g.toCochainMap
  comm := sorry

/-- The underlying cochain map of the identity module homomorphism is the identity. -/
@[simp]
theorem id_toCochainMap {𝒜 : DGA(𝒪)} (ℳ : Mod(𝒜, d)) :
    (id ℳ).toCochainMap = 𝟙 ℳ.toComplex := sorry

/-- The degree-`n` component of the identity module homomorphism is the identity. -/
@[simp]
theorem id_apply {𝒜 : DGA(𝒪)} (ℳ : Mod(𝒜, d)) (n : ℤ) :
    id ℳ n = 𝟙 (ℳ n) := sorry

/-- The underlying cochain map of a composite is the composite of underlying cochain maps. -/
@[simp]
theorem comp_toCochainMap {𝒜 : DGA(𝒪)} {ℳ N P : Mod(𝒜, d)}
    (f : Hom ℳ N) (g : Hom N P) :
    (comp f g).toCochainMap = f.toCochainMap ≫ g.toCochainMap := sorry

/-- The degree-`n` component of a composite is the composite of degree-`n` components. -/
@[simp]
theorem comp_apply {𝒜 : DGA(𝒪)} {ℳ N P : Mod(𝒜, d)}
    (f : Hom ℳ N) (g : Hom N P) (n : ℤ) :
    comp f g n = f n ≫ g n := sorry

end Hom

/-- The zero compatible cochain map between differential graded modules. -/
instance instZeroHom {𝒜 : DGA(𝒪)} (ℳ N : Mod(𝒜, d)) : Zero (Hom ℳ N) where
  zero :=
    { toCochainMap := 0
      comm := sorry }

/-- Compatible cochain maps make differential graded module sheaves into a category. -/
instance instCategory (𝒜 : DGA(𝒪)) : Category (Mod(𝒜, d)) where
  Hom ℳ N := Hom ℳ N
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- Differential graded module sheaves have canonical zero morphisms induced by zero cochain
maps. -/
@[stacks 0FSC "zero morphisms of differential graded modules"]
noncomputable instance hasZeroMorphisms (𝒜 : DGA(𝒪)) : HasZeroMorphisms Mod(𝒜, d) where
  zero ℳ N := instZeroHom ℳ N
  comp_zero := sorry
  zero_comp := sorry

/-- The underlying cochain map of the zero DG-module morphism is zero. -/
@[simp]
theorem zero_toCochainMap {𝒜 : DGA(𝒪)} (ℓ N : Mod(𝒜, d)) :
    (0 : ℓ ⟶ N).toCochainMap = 0 := sorry

/-- Definition 24.13.1 (3): the category of differential graded `𝒜`-module sheaves. -/
@[stacks 0FRI]
abbrev moduleCategory (𝒜 : DGA(𝒪)) := Mod(𝒜, d)

/-- The named module category is definitionally the bundled differential graded module type. -/
@[simp]
theorem moduleCategory_def (𝒜 : DGA(𝒪)) :
    moduleCategory 𝒜 = Mod(𝒜, d) := sorry

/-- Forget the differential graded module structure while retaining the cochain complex. -/
def forgetToComplex (𝒜 : DGA(𝒪)) : Mod(𝒜, d) ⥤ CpxO where
  obj ℳ := ℳ.toComplex
  map f := f.toCochainMap
  map_id := sorry
  map_comp := sorry

/-- Forgetting a differential graded module sheaf recovers its underlying cochain complex. -/
@[simp]
theorem forgetToComplex_obj {𝒜 : DGA(𝒪)} (ℳ : Mod(𝒜, d)) :
    (forgetToComplex 𝒜).obj ℳ = ℳ.toComplex := sorry

/-- Forgetting a differential graded module map recovers its underlying cochain map. -/
@[simp]
theorem forgetToComplex_map {𝒜 : DGA(𝒪)} {ℳ N : Mod(𝒜, d)} (f : ℳ ⟶ N) :
    (forgetToComplex 𝒜).map f = f.toCochainMap := sorry

/-- The degree-`n` component of the forgotten cochain map is the original degree-`n` component. -/
@[simp]
theorem forgetToComplex_map_f {𝒜 : DGA(𝒪)} {ℳ N : Mod(𝒜, d)} (f : ℳ ⟶ N) (n : ℤ) :
    ((forgetToComplex 𝒜).map f).f n = f.toCochainMap.f n := sorry

/-- Forgetting to cochain complexes is faithful. -/
instance forgetToComplex_faithful (𝒜 : DGA(𝒪)) : Functor.Faithful (forgetToComplex 𝒜) where
  map_injective := sorry

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
